//! Differential tests: the Lean fast specification of BLAKE2b, BLAKE2s and the EIP-152 `F`
//! precompile against `blake2b_simd`/`blake2s_simd`, RustCrypto's `blake2`, `revm-precompile`
//! and the `eip-152` crate.

use blake2::digest::{consts::U32, consts::U64, Mac, Update, VariableOutput};
use hash_lean::{Blake2Params, Blake2Variant};
use proptest::prelude::*;

fn simd_b(p: &Blake2Params, m: &[u8]) -> Vec<u8> {
    blake2b_simd::Params::new()
        .hash_length(p.out_len as usize)
        .key(p.key)
        .salt(p.salt)
        .personal(p.personal)
        .hash(m)
        .as_bytes()
        .to_vec()
}

fn simd_s(p: &Blake2Params, m: &[u8]) -> Vec<u8> {
    blake2s_simd::Params::new()
        .hash_length(p.out_len as usize)
        .key(p.key)
        .salt(p.salt)
        .personal(p.personal)
        .hash(m)
        .as_bytes()
        .to_vec()
}

/// RustCrypto `blake2`: unkeyed with any output length, or keyed with salt and
/// personalisation at the full output length.
fn rust_crypto_b(p: &Blake2Params, m: &[u8]) -> Option<Vec<u8>> {
    if p.key.is_empty() && p.salt.is_empty() && p.personal.is_empty() {
        let mut h = blake2::Blake2bVar::new(p.out_len as usize).ok()?;
        h.update(m);
        let mut out = vec![0u8; p.out_len as usize];
        h.finalize_variable(&mut out).ok()?;
        Some(out)
    } else if !p.key.is_empty() && p.out_len == 64 {
        let mut h =
            blake2::Blake2bMac::<U64>::new_with_salt_and_personal(p.key, p.salt, p.personal)
                .ok()?;
        Mac::update(&mut h, m);
        Some(h.finalize().into_bytes().to_vec())
    } else {
        None
    }
}

fn rust_crypto_s(p: &Blake2Params, m: &[u8]) -> Option<Vec<u8>> {
    if p.key.is_empty() && p.salt.is_empty() && p.personal.is_empty() {
        let mut h = blake2::Blake2sVar::new(p.out_len as usize).ok()?;
        h.update(m);
        let mut out = vec![0u8; p.out_len as usize];
        h.finalize_variable(&mut out).ok()?;
        Some(out)
    } else if !p.key.is_empty() && p.out_len == 32 {
        let mut h =
            blake2::Blake2sMac::<U32>::new_with_salt_and_personal(p.key, p.salt, p.personal)
                .ok()?;
        Mac::update(&mut h, m);
        Some(h.finalize().into_bytes().to_vec())
    } else {
        None
    }
}

fn check_b(p: &Blake2Params, m: &[u8]) {
    let n = m.len();
    let ours = hash_lean::blake2b(p, m);
    assert_eq!(ours, simd_b(p, m), "BLAKE2b vs blake2b_simd on {n} bytes, {p:?}");
    if let Some(theirs) = rust_crypto_b(p, m) {
        assert_eq!(ours, theirs, "BLAKE2b vs RustCrypto on {n} bytes, {p:?}");
    }
}

fn check_s(p: &Blake2Params, m: &[u8]) {
    let n = m.len();
    let ours = hash_lean::blake2s(p, m);
    assert_eq!(ours, simd_s(p, m), "BLAKE2s vs blake2s_simd on {n} bytes, {p:?}");
    if let Some(theirs) = rust_crypto_s(p, m) {
        assert_eq!(ours, theirs, "BLAKE2s vs RustCrypto on {n} bytes, {p:?}");
    }
}

/// The 213-byte EIP-152 input.
fn f_input(rounds: u32, h: &[u64; 8], m: &[u64; 16], t: [u64; 2], f: bool) -> Vec<u8> {
    let mut input = Vec::with_capacity(213);
    input.extend_from_slice(&rounds.to_be_bytes());
    for w in h.iter().chain(m.iter()).chain(t.iter()) {
        input.extend_from_slice(&w.to_le_bytes());
    }
    input.push(f as u8);
    input
}

fn revm_f(input: &[u8]) -> Option<Vec<u8>> {
    revm_precompile::blake2::run(input, u64::MAX)
        .ok()
        .map(|o| o.bytes.to_vec())
}

fn check_f(rounds: u32, h: &[u64; 8], m: &[u64; 16], t: [u64; 2], f: bool) {
    let input = f_input(rounds, h, m, t, f);
    let ours = hash_lean::blake2b_f(&input);
    assert_eq!(ours, revm_f(&input), "F vs revm, {rounds} rounds");
    let mut state = *h;
    eip_152::compress(&mut state, *m, t, f, rounds as usize);
    let theirs: Vec<u8> = state.iter().flat_map(|w| w.to_le_bytes()).collect();
    assert_eq!(ours, Some(theirs), "F vs eip-152, {rounds} rounds");
}

/// Every message length up to three blocks of BLAKE2b (128 bytes), unkeyed and keyed.
#[test]
fn all_lengths_up_to_three_blocks() {
    let key: Vec<u8> = (0..64).collect();
    for len in 0..=3 * 128 + 1 {
        let m: Vec<u8> = (0..len).map(|i| (i * 131 + 7) as u8).collect();
        for k in [0, 1, 32, 64] {
            check_b(&Blake2Params { out_len: 64, key: &key[..k], salt: &[], personal: &[] }, &m);
            check_s(
                &Blake2Params { out_len: 32, key: &key[..k / 2], salt: &[], personal: &[] },
                &m,
            );
        }
    }
}

/// Every output length, with and without salt and personalisation.
#[test]
fn all_output_lengths() {
    let m = b"The quick brown fox jumps over the lazy dog";
    for nn in 1..=64u8 {
        check_b(&Blake2Params { out_len: nn, key: &[], salt: &[], personal: &[] }, m);
        check_b(&Blake2Params { out_len: nn, key: b"key", salt: b"salt", personal: b"me" }, m);
    }
    for nn in 1..=32u8 {
        check_s(&Blake2Params { out_len: nn, key: &[], salt: &[], personal: &[] }, m);
        check_s(&Blake2Params { out_len: nn, key: b"key", salt: b"salt", personal: b"me" }, m);
    }
}

#[test]
fn one_mebibyte() {
    let m: Vec<u8> = (0..1usize << 20).map(|i| (i ^ (i >> 8)) as u8).collect();
    check_b(&Blake2Params { out_len: 64, key: &[], salt: &[], personal: &[] }, &m);
    check_s(&Blake2Params { out_len: 32, key: &[], salt: &[], personal: &[] }, &m);
}

/// The EIP-152 precompile on round counts from 0 to 100, plus invalid inputs.
#[test]
fn eip152_rounds_and_invalid_inputs() {
    let h: [u64; 8] = core::array::from_fn(|i| 0x0123_4567_89ab_cdef ^ (i as u64) << 40);
    let m: [u64; 16] = core::array::from_fn(|i| (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15));
    for rounds in 0..=100 {
        check_f(rounds, &h, &m, [rounds as u64, u64::MAX], rounds % 2 == 0);
    }
    let input = f_input(12, &h, &m, [0, 0], true);
    for len in [0, 1, 212, 214] {
        let mut bad = input.clone();
        bad.resize(len, 0);
        assert_eq!(hash_lean::blake2b_f(&bad), None, "length {len}");
        assert_eq!(revm_f(&bad), None, "length {len}");
    }
    for flag in 2..=255u8 {
        let mut bad = input.clone();
        bad[212] = flag;
        assert_eq!(hash_lean::blake2b_f(&bad), None, "flag {flag}");
        assert_eq!(revm_f(&bad), None, "flag {flag}");
    }
}

fn params_b() -> impl Strategy<Value = (u8, Vec<u8>, Vec<u8>, Vec<u8>)> {
    (
        1u8..=64,
        proptest::collection::vec(any::<u8>(), 0..=64),
        proptest::collection::vec(any::<u8>(), 0..=16),
        proptest::collection::vec(any::<u8>(), 0..=16),
    )
}

fn params_s() -> impl Strategy<Value = (u8, Vec<u8>, Vec<u8>, Vec<u8>)> {
    (
        1u8..=32,
        proptest::collection::vec(any::<u8>(), 0..=32),
        proptest::collection::vec(any::<u8>(), 0..=8),
        proptest::collection::vec(any::<u8>(), 0..=8),
    )
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]
    #[test]
    fn random_blake2b(m in proptest::collection::vec(any::<u8>(), 0..1024),
                      (nn, key, salt, personal) in params_b()) {
        check_b(&Blake2Params { out_len: nn, key: &key, salt: &salt, personal: &personal }, &m);
    }

    #[test]
    fn random_blake2s(m in proptest::collection::vec(any::<u8>(), 0..1024),
                      (nn, key, salt, personal) in params_s()) {
        check_s(&Blake2Params { out_len: nn, key: &key, salt: &salt, personal: &personal }, &m);
    }

    #[test]
    fn random_f(rounds in 0u32..64, h in any::<[u64; 8]>(), m in any::<[u64; 16]>(),
                t in any::<[u64; 2]>(), f in any::<bool>()) {
        check_f(rounds, &h, &m, t, f);
    }

    #[test]
    fn random_f_inputs(input in proptest::collection::vec(any::<u8>(), 0..300)) {
        // Mostly invalid inputs; keep the round count small when the length is right.
        let mut input = input;
        if input.len() >= 4 {
            input[0] = 0;
            input[1] = 0;
        }
        prop_assert_eq!(hash_lean::blake2b_f(&input), revm_f(&input));
    }

    /// Streaming in random pieces gives the one-shot output.
    #[test]
    fn streaming_matches_one_shot(
        m in proptest::collection::vec(any::<u8>(), 0..1024),
        pieces in proptest::collection::vec(0u16..300, 1..8),
        (nn, key, salt, personal) in params_s(),
    ) {
        let p = Blake2Params { out_len: nn, key: &key, salt: &salt, personal: &personal };
        prop_assert_eq!(hash_lean::blake2_stream(Blake2Variant::Blake2s, &p, &pieces, &m),
            simd_s(&p, &m));
        let p = Blake2Params { out_len: 2 * nn, ..p };
        prop_assert_eq!(hash_lean::blake2_stream(Blake2Variant::Blake2b, &p, &pieces, &m),
            simd_b(&p, &m));
    }
}
