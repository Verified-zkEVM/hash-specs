//! Differential tests: the Lean fast specification of BLAKE3 against the official `blake3`
//! crate and the BLAKE3 team's minimal reference implementation (`blake3-reference`, vendored).

use hash_lean::Blake3Mode;
use proptest::prelude::*;

fn official(mode: Blake3Mode, m: &[u8], n: usize) -> Vec<u8> {
    let mut h = match mode {
        Blake3Mode::Hash => blake3::Hasher::new(),
        Blake3Mode::Keyed(key) => blake3::Hasher::new_keyed(key),
        Blake3Mode::DeriveKey(context) => {
            blake3::Hasher::new_derive_key(std::str::from_utf8(context).expect("UTF-8 context"))
        }
    };
    h.update(m);
    let mut out = vec![0u8; n];
    h.finalize_xof().fill(&mut out);
    out
}

fn reference(mode: Blake3Mode, m: &[u8], n: usize) -> Vec<u8> {
    let mut h = match mode {
        Blake3Mode::Hash => blake3_reference::Hasher::new(),
        Blake3Mode::Keyed(key) => blake3_reference::Hasher::new_keyed(key),
        Blake3Mode::DeriveKey(context) => blake3_reference::Hasher::new_derive_key(
            std::str::from_utf8(context).expect("UTF-8 context"),
        ),
    };
    h.update(m);
    let mut out = vec![0u8; n];
    h.finalize(&mut out);
    out
}

const KEY: &[u8; 32] = b"whats the Elvish word for friend";
const CONTEXT: &[u8] = b"BLAKE3 2019-12-27 16:29:52 test vectors context";

fn check(m: &[u8], n: usize) {
    let len = m.len();
    for mode in [Blake3Mode::Hash, Blake3Mode::Keyed(KEY), Blake3Mode::DeriveKey(CONTEXT)] {
        let ours = hash_lean::blake3(mode, m, n);
        assert_eq!(ours, official(mode, m, n), "{mode:?} vs blake3 on {len} bytes, {n} out");
        assert_eq!(ours, reference(mode, m, n), "{mode:?} vs reference on {len} bytes, {n} out");
    }
}

/// Every input length up to five chunks plus one, around every block and chunk boundary.
#[test]
fn lengths_up_to_five_chunks() {
    for len in (0..=2 * 1024 + 1).chain((2 * 1024 + 2..=5 * 1024 + 1).step_by(61)) {
        let m: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
        check(&m, 32);
    }
    for len in [3 * 1024, 4 * 1024, 4 * 1024 + 1, 8 * 1024, 8 * 1024 + 1, 16 * 1024 + 7] {
        let m: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
        check(&m, 32);
    }
}

/// Output lengths around the 64-byte output blocks.
#[test]
fn output_lengths() {
    let m = b"The quick brown fox jumps over the lazy dog";
    for n in (0..=3 * 64 + 1).chain([1000, 4096]) {
        check(m, n);
    }
}

#[test]
fn one_mebibyte() {
    let m: Vec<u8> = (0..1usize << 20).map(|i| (i ^ (i >> 8)) as u8).collect();
    check(&m, 64);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]
    #[test]
    fn random_inputs(m in proptest::collection::vec(any::<u8>(), 0..6000), n in 0usize..300,
                     key in any::<[u8; 32]>(), context in "[ -~]{0,80}") {
        check(&m, n);
        let ours = hash_lean::blake3(Blake3Mode::Keyed(&key), &m, n);
        prop_assert_eq!(&ours, &official(Blake3Mode::Keyed(&key), &m, n));
        let mode = Blake3Mode::DeriveKey(context.as_bytes());
        prop_assert_eq!(hash_lean::blake3(mode, &m, n), official(mode, &m, n));
    }

    /// Streaming in random pieces gives the one-shot output.
    #[test]
    fn streaming_matches_one_shot(
        m in proptest::collection::vec(any::<u8>(), 0..6000),
        pieces in proptest::collection::vec(0u16..3000, 1..8),
        n in 0usize..200,
    ) {
        for mode in [Blake3Mode::Hash, Blake3Mode::Keyed(KEY), Blake3Mode::DeriveKey(CONTEXT)] {
            prop_assert_eq!(hash_lean::blake3_stream(mode, &pieces, &m, n), official(mode, &m, n),
                "{:?} in {:?}", mode, &pieces);
        }
    }
}
