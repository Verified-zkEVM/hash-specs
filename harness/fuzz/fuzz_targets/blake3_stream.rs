//! Coverage-guided fuzzing of the BLAKE3 streaming interface: a message added in pieces of
//! fuzzer-chosen sizes must give the output of the BLAKE3 team's reference implementation.
//!
//! Input layout: a piece count `k` (at most 15), `k` big-endian 16-bit piece sizes, a
//! big-endian 16-bit output length, then the message.

#![no_main]

use hash_lean::Blake3Mode;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Some((&k, rest)) = data.split_first() else { return };
    let k = (k % 16) as usize;
    if rest.len() < 2 * k + 2 {
        return;
    }
    let pieces: Vec<u16> =
        rest[..2 * k].chunks(2).map(|c| u16::from_be_bytes([c[0], c[1]]) % 4096).collect();
    let pieces = if pieces.is_empty() { vec![1] } else { pieces };
    let n = u16::from_be_bytes([rest[2 * k], rest[2 * k + 1]]) as usize % 600;
    let m = &rest[2 * k + 2..];
    let mut h = blake3_reference::Hasher::new();
    h.update(m);
    let mut expected = vec![0u8; n];
    h.finalize(&mut expected);
    assert_eq!(hash_lean::blake3_stream(Blake3Mode::Hash, &pieces, m, n), expected, "in {pieces:?}");
});
