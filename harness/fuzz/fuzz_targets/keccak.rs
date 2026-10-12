//! Coverage-guided differential fuzzing of SHA-3, SHAKE and Keccak-256: the Lean fast
//! specification against RustCrypto's `sha3`, `tiny-keccak` and AWS-LC.
//!
//! The first two input bytes choose the SHAKE output length (big-endian, at most 1023 bytes);
//! the rest is the message.

#![no_main]

use aws_lc_rs::digest;
use libfuzzer_sys::fuzz_target;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::Digest;
use tiny_keccak::{Hasher, Xof};

fuzz_target!(|data: &[u8]| {
    let (d, m) = match data {
        [hi, lo, rest @ ..] => ((u16::from_be_bytes([*hi, *lo]) % 1024) as usize, rest),
        _ => (32, data),
    };

    let ours = hash_lean::sha3_256(m);
    assert_eq!(ours, sha3::Sha3_256::digest(m).as_slice(), "SHA3-256 vs RustCrypto");
    assert_eq!(ours, digest::digest(&digest::SHA3_256, m).as_ref(), "SHA3-256 vs AWS-LC");
    assert_eq!(hash_lean::sha3_224(m), sha3::Sha3_224::digest(m).as_slice(), "SHA3-224");
    let ours = hash_lean::sha3_384(m);
    assert_eq!(ours, sha3::Sha3_384::digest(m).as_slice(), "SHA3-384 vs RustCrypto");
    assert_eq!(ours, digest::digest(&digest::SHA3_384, m).as_ref(), "SHA3-384 vs AWS-LC");
    let ours = hash_lean::sha3_512(m);
    assert_eq!(ours, sha3::Sha3_512::digest(m).as_slice(), "SHA3-512 vs RustCrypto");
    assert_eq!(ours, digest::digest(&digest::SHA3_512, m).as_ref(), "SHA3-512 vs AWS-LC");

    let ours = hash_lean::keccak256(m);
    assert_eq!(ours, sha3::Keccak256::digest(m).as_slice(), "Keccak-256 vs RustCrypto");
    let mut k = tiny_keccak::Keccak::v256();
    k.update(m);
    let mut out = [0u8; 32];
    k.finalize(&mut out);
    assert_eq!(ours, out, "Keccak-256 vs tiny-keccak");

    let ours = hash_lean::shake128(m, d);
    let mut h = sha3::Shake128::default();
    h.update(m);
    let mut expected = vec![0u8; d];
    h.finalize_xof().read(&mut expected);
    assert_eq!(ours, expected, "SHAKE128 vs RustCrypto");
    let mut t = tiny_keccak::Shake::v128();
    t.update(m);
    t.squeeze(&mut expected);
    assert_eq!(ours, expected, "SHAKE128 vs tiny-keccak");

    let ours = hash_lean::shake256(m, d);
    let mut h = sha3::Shake256::default();
    h.update(m);
    let mut expected = vec![0u8; d];
    h.finalize_xof().read(&mut expected);
    assert_eq!(ours, expected, "SHAKE256 vs RustCrypto");
});
