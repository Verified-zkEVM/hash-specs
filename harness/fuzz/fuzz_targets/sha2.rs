//! Coverage-guided differential fuzzing of SHA-2: the Lean fast specification against
//! RustCrypto's `sha2` and AWS-LC.

#![no_main]

use aws_lc_rs::digest;
use libfuzzer_sys::fuzz_target;
use sha2::Digest;

fuzz_target!(|m: &[u8]| {
    let ours = hash_lean::sha256(m);
    assert_eq!(ours, sha2::Sha256::digest(m).as_slice(), "SHA-256 vs RustCrypto");
    assert_eq!(ours, digest::digest(&digest::SHA256, m).as_ref(), "SHA-256 vs AWS-LC");

    assert_eq!(hash_lean::sha224(m), sha2::Sha224::digest(m).as_slice(), "SHA-224 vs RustCrypto");

    let ours = hash_lean::sha512(m);
    assert_eq!(ours, sha2::Sha512::digest(m).as_slice(), "SHA-512 vs RustCrypto");
    assert_eq!(ours, digest::digest(&digest::SHA512, m).as_ref(), "SHA-512 vs AWS-LC");

    let ours = hash_lean::sha384(m);
    assert_eq!(ours, sha2::Sha384::digest(m).as_slice(), "SHA-384 vs RustCrypto");
    assert_eq!(ours, digest::digest(&digest::SHA384, m).as_ref(), "SHA-384 vs AWS-LC");

    assert_eq!(hash_lean::sha512_224(m), sha2::Sha512_224::digest(m).as_slice(), "SHA-512/224");
    let ours = hash_lean::sha512_256(m);
    assert_eq!(ours, sha2::Sha512_256::digest(m).as_slice(), "SHA-512/256 vs RustCrypto");
    assert_eq!(ours, digest::digest(&digest::SHA512_256, m).as_ref(), "SHA-512/256 vs AWS-LC");
});
