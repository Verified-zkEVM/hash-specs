//! Differential tests: the Lean fast specification of SHA-2 against two independent
//! implementations, RustCrypto's `sha2` and AWS-LC (`aws-lc-rs`).

use aws_lc_rs::digest;
use proptest::prelude::*;
use sha2::Digest;

/// A SHA-2 variant: its Lean, RustCrypto and AWS-LC implementations.
struct Variant {
    name: &'static str,
    lean: fn(&[u8]) -> Vec<u8>,
    rust_crypto: fn(&[u8]) -> Vec<u8>,
    aws_lc: Option<&'static digest::Algorithm>,
}

fn variants() -> Vec<Variant> {
    vec![
        Variant { name: "SHA-224", lean: hash_lean::sha224, rust_crypto: |m| sha2::Sha224::digest(m).to_vec(), aws_lc: None },
        Variant { name: "SHA-256", lean: hash_lean::sha256, rust_crypto: |m| sha2::Sha256::digest(m).to_vec(), aws_lc: Some(&digest::SHA256) },
        Variant { name: "SHA-384", lean: hash_lean::sha384, rust_crypto: |m| sha2::Sha384::digest(m).to_vec(), aws_lc: Some(&digest::SHA384) },
        Variant { name: "SHA-512", lean: hash_lean::sha512, rust_crypto: |m| sha2::Sha512::digest(m).to_vec(), aws_lc: Some(&digest::SHA512) },
        Variant { name: "SHA-512/224", lean: hash_lean::sha512_224, rust_crypto: |m| sha2::Sha512_224::digest(m).to_vec(), aws_lc: None },
        Variant { name: "SHA-512/256", lean: hash_lean::sha512_256, rust_crypto: |m| sha2::Sha512_256::digest(m).to_vec(), aws_lc: Some(&digest::SHA512_256) },
    ]
}

fn check(m: &[u8]) {
    for v in variants() {
        let ours = (v.lean)(m);
        assert_eq!(ours, (v.rust_crypto)(m), "{} disagrees with RustCrypto on {} bytes", v.name, m.len());
        if let Some(alg) = v.aws_lc {
            assert_eq!(ours, digest::digest(alg, m).as_ref(), "{} disagrees with AWS-LC on {} bytes", v.name, m.len());
        }
    }
}

/// Every message length up to three 1024-bit blocks, covering all the padding boundaries
/// (55/56/64 bytes for SHA-256, 111/112/128 bytes for SHA-512).
#[test]
fn all_lengths_up_to_three_blocks() {
    for len in 0..=3 * 128 + 1 {
        let m: Vec<u8> = (0..len).map(|i| (i * 131 + 7) as u8).collect();
        check(&m);
    }
}

#[test]
fn one_mebibyte() {
    let m: Vec<u8> = (0..1usize << 20).map(|i| (i ^ (i >> 8)) as u8).collect();
    check(&m);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]
    #[test]
    fn random_messages(m in proptest::collection::vec(any::<u8>(), 0..4096)) {
        check(&m);
    }
}

#[test]
fn many_threads() {
    let handles: Vec<_> = (0..8)
        .map(|t| std::thread::spawn(move || {
            for len in 0..200usize {
                let m: Vec<u8> = (0..len).map(|i| (i + t) as u8).collect();
                check(&m);
            }
        }))
        .collect();
    for h in handles {
        h.join().unwrap();
    }
}
