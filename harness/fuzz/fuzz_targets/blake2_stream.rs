//! Coverage-guided fuzzing of the BLAKE2 streaming interface: a message added in pieces of
//! fuzzer-chosen sizes must give the output of `blake2b_simd` or `blake2s_simd`.
//!
//! Input layout: a variant byte, a piece count `k` (at most 15), `k` big-endian 16-bit piece
//! sizes, an output-length byte, a key-length byte, the key, then the message.

#![no_main]

use hash_lean::{Blake2Params, Blake2Variant};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() < 2 {
        return;
    }
    let blake2b = data[0] % 2 == 0;
    let k = (data[1] % 16) as usize;
    let rest = &data[2..];
    if rest.len() < 2 * k + 2 {
        return;
    }
    let pieces: Vec<u16> =
        rest[..2 * k].chunks(2).map(|c| u16::from_be_bytes([c[0], c[1]]) % 512).collect();
    let pieces = if pieces.is_empty() { vec![1] } else { pieces };
    let (max, variant) =
        if blake2b { (64, Blake2Variant::Blake2b) } else { (32, Blake2Variant::Blake2s) };
    let out_len = rest[2 * k] % max + 1;
    let kk = rest[2 * k + 1] as usize % (max as usize + 1);
    let rest = &rest[2 * k + 2..];
    if rest.len() < kk {
        return;
    }
    let (key, m) = rest.split_at(kk);
    let p = Blake2Params { out_len, key, salt: &[], personal: &[] };
    let expected = if blake2b {
        blake2b_simd::Params::new().hash_length(out_len as usize).key(key).hash(m).as_bytes().to_vec()
    } else {
        blake2s_simd::Params::new().hash_length(out_len as usize).key(key).hash(m).as_bytes().to_vec()
    };
    assert_eq!(hash_lean::blake2_stream(variant, &p, &pieces, m), expected, "{variant:?} in {pieces:?}");
});
