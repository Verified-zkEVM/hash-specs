//! Coverage-guided fuzzing of the SHA-2 streaming interface: a message absorbed in pieces of
//! fuzzer-chosen sizes must give the one-shot digest of RustCrypto's `sha2`.
//!
//! Input layout: a variant byte, a piece count `k` (at most 15), `k` big-endian 16-bit piece
//! sizes, then the message.

#![no_main]

use hash_lean::Sha2Variant;
use libfuzzer_sys::fuzz_target;
use sha2::Digest;

fuzz_target!(|data: &[u8]| {
    if data.len() < 2 {
        return;
    }
    let variant = Sha2Variant::ALL[data[0] as usize % 6];
    let k = (data[1] % 16) as usize;
    let Some(rest) = data.get(2..) else { return };
    if rest.len() < 2 * k {
        return;
    }
    // Keep piece sizes small enough that a typical input is split several times.
    let pieces: Vec<u16> =
        rest[..2 * k].chunks(2).map(|c| u16::from_be_bytes([c[0], c[1]]) % 512).collect();
    let pieces = if pieces.is_empty() { vec![1] } else { pieces };
    let m = &rest[2 * k..];
    let expected = match variant {
        Sha2Variant::Sha224 => sha2::Sha224::digest(m).to_vec(),
        Sha2Variant::Sha256 => sha2::Sha256::digest(m).to_vec(),
        Sha2Variant::Sha384 => sha2::Sha384::digest(m).to_vec(),
        Sha2Variant::Sha512 => sha2::Sha512::digest(m).to_vec(),
        Sha2Variant::Sha512_224 => sha2::Sha512_224::digest(m).to_vec(),
        Sha2Variant::Sha512_256 => sha2::Sha512_256::digest(m).to_vec(),
    };
    assert_eq!(hash_lean::sha2_stream(variant, &pieces, m), expected, "{variant:?} in {pieces:?}");
});
