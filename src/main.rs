
use std::convert::TryInto;
use std::fs::OpenOptions;
use std::io::{Read, Write, Seek, SeekFrom};
use std::env;

use rand::Rng;
use rand_core::OsRng;
use rpassword::read_password;
use zeroize::Zeroize;  // <--- Zeroize import

use argon2::{Argon2, Algorithm, Params, Version};
use hmac::{Hmac, Mac};
use sha2::Sha512;

// HMAC alias
type HmacSha512 = Hmac<Sha512>;

// ================================
// Threefish-512 Implementation
// ================================
struct Threefish512 {
    key: [u64; 8],
    tweak: [u64; 2],
}

/// Rotation constants for Threefish-512 (72 rounds).
const ROTATION_CONSTANTS: [[u64; 4]; 8] = [
    [46, 36, 19, 37],
    [33, 27, 14, 42],
    [17, 49, 36, 39],
    [44,  9, 54, 56],
    [39, 30, 34, 24],
    [13, 50, 10, 17],
    [25, 29, 39, 43],
    [ 8, 35, 56, 22],
];

#[inline(always)]
fn mix(a: u64, b: u64, r: u64) -> (u64, u64) {
    let a_new = a.wrapping_add(b);
    let b_new = b.rotate_left(r as u32) ^ a_new;
    (a_new, b_new)
}

impl Threefish512 {
    fn new(key: [u64; 8], tweak: [u64; 2]) -> Self {
        Self { key, tweak }
    }

    fn encrypt_block(&self, block: &mut [u64; 8]) {
        let mut v = *block;
        let mut ks = [0u64; 9];
        let mut t = [0u64; 3];

        // Parity
        let mut parity = 0u64;
        for &k in &self.key {
            parity ^= k;
        }
        ks[..8].copy_from_slice(&self.key);
        ks[8] = parity;

        t[0] = self.tweak[0];
        t[1] = self.tweak[1];
        t[2] = self.tweak[0] ^ self.tweak[1];

        for round in 0..72 {
            if round % 4 == 0 {
                let s = round % 8;
                v[0] = v[0].wrapping_add(ks[(s + 0) % 9]);
                v[1] = v[1].wrapping_add(ks[(s + 1) % 9]);
                v[2] = v[2].wrapping_add(ks[(s + 2) % 9]);
                v[3] = v[3].wrapping_add(ks[(s + 3) % 9]);
                v[4] = v[4].wrapping_add(ks[(s + 4) % 9]);
                v[5] = v[5]
                    .wrapping_add(ks[(s + 5) % 9])
                    .wrapping_add(t[(round / 4) % 3]);
                v[6] = v[6]
                    .wrapping_add(ks[(s + 6) % 9])
                    .wrapping_add(t[((round / 4) + 1) % 3]);
                v[7] = v[7].wrapping_add(ks[(s + 7) % 9]).wrapping_add(round as u64);
            }

            let rc = ROTATION_CONSTANTS[round as usize % 8];
            let (n0, n1) = mix(v[0], v[1], rc[0]);
            v[0] = n0; 
            v[1] = n1;
            let (n2, n3) = mix(v[2], v[3], rc[1]);
            v[2] = n2; 
            v[3] = n3;
            let (n4, n5) = mix(v[4], v[5], rc[2]);
            v[4] = n4; 
            v[5] = n5;
            let (n6, n7) = mix(v[6], v[7], rc[3]);
            v[6] = n6; 
            v[7] = n7;

            // Permutation
            v = [
                v[0], v[3], v[2], v[1],
                v[4], v[7], v[6], v[5],
            ];
        }

        // Final key injection
        let s = 72 % 8; // = 0
        v[0] = v[0].wrapping_add(ks[(s + 0) % 9]);
        v[1] = v[1].wrapping_add(ks[(s + 1) % 9]);
        v[2] = v[2].wrapping_add(ks[(s + 2) % 9]);
        v[3] = v[3].wrapping_add(ks[(s + 3) % 9]);
        v[4] = v[4].wrapping_add(ks[(s + 4) % 9]);
        v[5] = v[5]
            .wrapping_add(ks[(s + 5) % 9])
            .wrapping_add(t[(72 / 4) % 3]);
        v[6] = v[6]
            .wrapping_add(ks[(s + 6) % 9])
            .wrapping_add(t[((72 / 4) + 1) % 3]);
        v[7] = v[7].wrapping_add(ks[(s + 7) % 9]).wrapping_add(72);

        *block = v;
    }
}

// -- The key difference: we define build_tweak and threefish_ctr_xor_block properly:

fn build_tweak(nonce: &[u8; 16], counter: u64) -> [u64; 2] {
    let mut t = [0u64; 2];
    t[0] = u64::from_le_bytes(nonce[0..8].try_into().unwrap());
    let mut second = u64::from_le_bytes(nonce[8..16].try_into().unwrap());
    second ^= counter;
    t[1] = second;
    t
}

fn threefish_ctr_xor_block(key: &[u64; 8], tweak: &[u64; 2], input_block: &mut [u8]) {
    let mut zero_block = [0u64; 8];
    let tf = Threefish512::new(*key, *tweak);
    tf.encrypt_block(&mut zero_block);

    // XOR the 64-byte keystream into input_block
    let keystream_bytes = zero_block.iter()
        .flat_map(|&word| word.to_le_bytes().to_vec())
        .collect::<Vec<u8>>();
    for (i, b) in input_block.iter_mut().enumerate() {
        *b ^= keystream_bytes[i];
    }
}

// ================================
// CTR + HMAC
// ================================
fn encrypt_data(master_key: &[u8; 128], nonce: &[u8; 16], plaintext: &[u8]) -> Vec<u8> {
    let (tf_key_bytes, hmac_key) = master_key.split_at(64);

    // Convert to [u64; 8]
    let mut tf_key = [0u64; 8];
    for (i, chunk) in tf_key_bytes.chunks(8).enumerate() {
        tf_key[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }

    // CTR encryption
    let mut ciphertext = plaintext.to_vec();
    let block_size = 64;
    let mut counter = 0u64;
    let mut offset = 0;
    while offset < ciphertext.len() {
        let end = offset + block_size.min(ciphertext.len() - offset);
        let tweak = build_tweak(nonce, counter);
        threefish_ctr_xor_block(&tf_key, &tweak, &mut ciphertext[offset..end]);
        offset = end;
        counter = counter.wrapping_add(1);
    }

    // HMAC over (nonce || ciphertext)
    let mut mac = HmacSha512::new_from_slice(hmac_key).expect("HMAC key error");
    mac.update(nonce);
    mac.update(&ciphertext);
    let tag = mac.finalize().into_bytes(); // 64 bytes

    // Combine
    let mut out = Vec::with_capacity(ciphertext.len() + 64);
    out.extend_from_slice(&ciphertext);
    out.extend_from_slice(&tag);
    out
}

fn decrypt_data(
    master_key: &[u8; 128],
    nonce: &[u8; 16],
    ciphertext_and_tag: &[u8],
) -> Result<Vec<u8>, String> {
    if ciphertext_and_tag.len() < 64 {
        return Err("Ciphertext too short".to_string());
    }
    let (ciphertext, tag) = ciphertext_and_tag.split_at(ciphertext_and_tag.len() - 64);

    let (tf_key_bytes, hmac_key) = master_key.split_at(64);

    // Convert to [u64; 8]
    let mut tf_key = [0u64; 8];
    for (i, chunk) in tf_key_bytes.chunks(8).enumerate() {
        tf_key[i] = u64::from_le_bytes(chunk.try_into().unwrap());
    }

    // Verify HMAC
    let mut mac = HmacSha512::new_from_slice(hmac_key)
        .map_err(|_| "Invalid HMAC key".to_string())?;
    mac.update(nonce);
    mac.update(ciphertext);
    mac.verify_slice(tag).map_err(|_| "HMAC mismatch".to_string())?;

    // Decrypt
    let mut plaintext = ciphertext.to_vec();
    let block_size = 64;
    let mut counter = 0u64;
    let mut offset = 0;
    while offset < plaintext.len() {
        let end = offset + block_size.min(plaintext.len() - offset);
        let tweak = build_tweak(nonce, counter);
        threefish_ctr_xor_block(&tf_key, &tweak, &mut plaintext[offset..end]);
        offset = end;
        counter = counter.wrapping_add(1);
    }

    Ok(plaintext)
}

// ================================
// Argon2 Key Derivation Example
// ================================
fn derive_key_128(password: &str, salt: &[u8]) -> [u8; 128] {
    let params = Params::new(65536, 3, 4, Some(128))
        .expect("Invalid Argon2 params");

    let argon2 = Argon2::new(Algorithm::Argon2id, Version::V0x13, params);

    let mut out = [0u8; 128];
    argon2
        .hash_password_into(password.as_bytes(), salt, &mut out)
        .expect("Argon2 hashing failed");
    out
}

// ================================
// Main CLI Logic (Minimal Demo)
// ================================
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <filename>", args[0]);
        std::process::exit(1);
    }
    let filename = &args[1];

    // 1) Get password from user
    print!("Enter password: ");
    std::io::Write::flush(&mut std::io::stdout())?;
    let pass1 = read_password()?;

    print!("Repeat password: ");
    std::io::Write::flush(&mut std::io::stdout())?;
    let pass2 = read_password()?;
    if pass1 != pass2 {
        eprintln!("Passwords do not match!");
        std::process::exit(1);
    }

    // 2) Open file, check if it starts with "TFSH"
    let mut file = OpenOptions::new().read(true).write(true).open(filename)?;

    let mut magic = [0u8; 4];
    let n = file.read(&mut magic)?;
    file.seek(SeekFrom::Start(0))?;

    const MAGIC: &[u8] = b"TFSH";

    if n == 4 && magic == MAGIC {
        // DECRYPT
        // read the entire file
        let mut file_data = Vec::new();
        file.read_to_end(&mut file_data)?;

        // file_data layout: 0..4 = "TFSH", 4..20 = salt, 20..36 = nonce, 36..EOF-64 = ciphertext, EOF-64..EOF = tag
        if file_data.len() < 36 + 64 {
            eprintln!("File too small to be valid encrypted data.");
            std::process::exit(1);
        }
        let salt = &file_data[4..20];
        let nonce = &file_data[20..36];
        let ciphertext_tag = &file_data[36..];

        // derive key
        let mut master_key = derive_key_128(&pass1, salt);

        // decrypt
        match decrypt_data(&master_key, nonce.try_into().unwrap(), ciphertext_tag) {
            Ok(plaintext) => {
                // overwrite file
                file.set_len(0)?;
                file.seek(SeekFrom::Start(0))?;
                file.write_all(&plaintext)?;

                // zeroize the key
                master_key.zeroize();
            }
            Err(e) => {
                eprintln!("Decryption error: {e}");
                master_key.zeroize();
                std::process::exit(1);
            }
        }
    } else {
        // ENCRYPT
        let mut plaintext = Vec::new();
        file.read_to_end(&mut plaintext)?;

        let mut salt = [0u8; 16];
        let mut nonce = [0u8; 16];
        OsRng.fill(&mut salt);
        OsRng.fill(&mut nonce);

        let mut master_key = derive_key_128(&pass1, &salt);

        // encrypt
        let ciphertext_tag = encrypt_data(&master_key, &nonce, &plaintext);

        // overwrite file
        file.set_len(0)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(MAGIC)?;
        file.write_all(&salt)?;
        file.write_all(&nonce)?;
        file.write_all(&ciphertext_tag)?;

        // zeroize the key
        master_key.zeroize();
    }

    Ok(())
}

