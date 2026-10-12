//! Differential tests: the Lean fast specification of SHA-3, SHAKE and Keccak-256 against
//! RustCrypto's `sha3`, `tiny-keccak`, AWS-LC (`aws-lc-rs`) and, for Keccak-256,
//! `alloy-primitives`.

use aws_lc_rs::digest;
use proptest::prelude::*;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::Digest;
use tiny_keccak::Hasher;

fn tiny<H: Hasher>(mut h: H, m: &[u8], n: usize) -> Vec<u8> {
    h.update(m);
    let mut out = vec![0u8; n];
    h.finalize(&mut out);
    out
}

fn tiny_xof<H: tiny_keccak::Xof + Hasher>(mut h: H, m: &[u8], n: usize) -> Vec<u8> {
    h.update(m);
    let mut out = vec![0u8; n];
    h.squeeze(&mut out);
    out
}

fn rust_crypto_xof<H: Default + Update + ExtendableOutput>(m: &[u8], n: usize) -> Vec<u8> {
    let mut h = H::default();
    h.update(m);
    let mut out = vec![0u8; n];
    h.finalize_xof().read(&mut out);
    out
}

fn check(m: &[u8]) {
    let n = m.len();
    let ours = hash_lean::sha3_224(m);
    assert_eq!(ours, sha3::Sha3_224::digest(m).to_vec(), "SHA3-224 vs RustCrypto on {n} bytes");
    assert_eq!(ours, tiny(tiny_keccak::Sha3::v224(), m, 28), "SHA3-224 vs tiny-keccak on {n} bytes");

    let ours = hash_lean::sha3_256(m);
    assert_eq!(ours, sha3::Sha3_256::digest(m).to_vec(), "SHA3-256 vs RustCrypto on {n} bytes");
    assert_eq!(ours, tiny(tiny_keccak::Sha3::v256(), m, 32), "SHA3-256 vs tiny-keccak on {n} bytes");
    assert_eq!(ours, digest::digest(&digest::SHA3_256, m).as_ref(), "SHA3-256 vs AWS-LC on {n} bytes");

    let ours = hash_lean::sha3_384(m);
    assert_eq!(ours, sha3::Sha3_384::digest(m).to_vec(), "SHA3-384 vs RustCrypto on {n} bytes");
    assert_eq!(ours, tiny(tiny_keccak::Sha3::v384(), m, 48), "SHA3-384 vs tiny-keccak on {n} bytes");
    assert_eq!(ours, digest::digest(&digest::SHA3_384, m).as_ref(), "SHA3-384 vs AWS-LC on {n} bytes");

    let ours = hash_lean::sha3_512(m);
    assert_eq!(ours, sha3::Sha3_512::digest(m).to_vec(), "SHA3-512 vs RustCrypto on {n} bytes");
    assert_eq!(ours, tiny(tiny_keccak::Sha3::v512(), m, 64), "SHA3-512 vs tiny-keccak on {n} bytes");
    assert_eq!(ours, digest::digest(&digest::SHA3_512, m).as_ref(), "SHA3-512 vs AWS-LC on {n} bytes");

    let ours = hash_lean::keccak256(m);
    assert_eq!(ours, sha3::Keccak256::digest(m).to_vec(), "Keccak-256 vs RustCrypto on {n} bytes");
    assert_eq!(ours, tiny(tiny_keccak::Keccak::v256(), m, 32), "Keccak-256 vs tiny-keccak on {n} bytes");
    assert_eq!(ours, alloy_primitives::keccak256(m).to_vec(), "Keccak-256 vs alloy on {n} bytes");
}

fn check_xof(m: &[u8], d: usize) {
    let n = m.len();
    let ours = hash_lean::shake128(m, d);
    assert_eq!(ours, rust_crypto_xof::<sha3::Shake128>(m, d), "SHAKE128 vs RustCrypto, {n} bytes in, {d} out");
    assert_eq!(ours, tiny_xof(tiny_keccak::Shake::v128(), m, d), "SHAKE128 vs tiny-keccak, {n} bytes in, {d} out");
    let ours = hash_lean::shake256(m, d);
    assert_eq!(ours, rust_crypto_xof::<sha3::Shake256>(m, d), "SHAKE256 vs RustCrypto, {n} bytes in, {d} out");
    assert_eq!(ours, tiny_xof(tiny_keccak::Shake::v256(), m, d), "SHAKE256 vs tiny-keccak, {n} bytes in, {d} out");
}

/// Every message length up to three blocks of the largest rate (168 bytes), covering every
/// rate boundary (72, 104, 136, 144 and 168 bytes).
#[test]
fn all_lengths_up_to_three_blocks() {
    for len in 0..=3 * 168 + 1 {
        let m: Vec<u8> = (0..len).map(|i| (i * 131 + 7) as u8).collect();
        check(&m);
    }
}

/// Output lengths around the rate boundaries, for the extendable-output functions.
#[test]
fn xof_output_lengths() {
    let m = b"The quick brown fox jumps over the lazy dog";
    for d in (0..=3 * 168 + 1).chain([1000, 4096]) {
        check_xof(m, d);
    }
}

#[test]
fn one_mebibyte() {
    let m: Vec<u8> = (0..1usize << 20).map(|i| (i ^ (i >> 8)) as u8).collect();
    check(&m);
    check_xof(&m, 200);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]
    #[test]
    fn random_messages(m in proptest::collection::vec(any::<u8>(), 0..2048)) {
        check(&m);
    }

    #[test]
    fn random_xof(m in proptest::collection::vec(any::<u8>(), 0..512), d in 0usize..1024) {
        check_xof(&m, d);
    }

    /// Streaming in random pieces gives the one-shot output.
    #[test]
    fn streaming_matches_one_shot(
        m in proptest::collection::vec(any::<u8>(), 0..1024),
        pieces in proptest::collection::vec(0u16..400, 1..8),
        d in 0u16..600,
    ) {
        use hash_lean::KeccakVariant::*;
        for v in hash_lean::KeccakVariant::ALL {
            let expected = match v {
                Sha3_224 => hash_lean::sha3_224(&m),
                Sha3_256 => hash_lean::sha3_256(&m),
                Sha3_384 => hash_lean::sha3_384(&m),
                Sha3_512 => hash_lean::sha3_512(&m),
                Shake128 => rust_crypto_xof::<sha3::Shake128>(&m, d as usize),
                Shake256 => rust_crypto_xof::<sha3::Shake256>(&m, d as usize),
                Keccak256 => sha3::Keccak256::digest(&m).to_vec(),
            };
            prop_assert_eq!(hash_lean::keccak_stream(v, &pieces, &m, d), expected, "{:?} in {:?}", v, &pieces);
        }
    }
}
