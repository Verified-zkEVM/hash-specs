//! Coverage-guided fuzzing of the Keccak streaming interface: a message absorbed in pieces of
//! fuzzer-chosen sizes must give the one-shot output of RustCrypto's `sha3`.
//!
//! Input layout: a variant byte, a piece count `k` (at most 15), `k` big-endian 16-bit piece
//! sizes, a big-endian 16-bit SHAKE output length, then the message.

#![no_main]

use hash_lean::KeccakVariant;
use libfuzzer_sys::fuzz_target;
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::Digest;

fn xof<H: Default + Update + ExtendableOutput>(m: &[u8], n: usize) -> Vec<u8> {
    let mut h = H::default();
    h.update(m);
    let mut out = vec![0u8; n];
    h.finalize_xof().read(&mut out);
    out
}

fuzz_target!(|data: &[u8]| {
    if data.len() < 2 {
        return;
    }
    let variant = KeccakVariant::ALL[data[0] as usize % 7];
    let k = (data[1] % 16) as usize;
    let Some(rest) = data.get(2..) else { return };
    if rest.len() < 2 * k + 2 {
        return;
    }
    let pieces: Vec<u16> =
        rest[..2 * k].chunks(2).map(|c| u16::from_be_bytes([c[0], c[1]]) % 512).collect();
    let pieces = if pieces.is_empty() { vec![1] } else { pieces };
    let d = u16::from_be_bytes([rest[2 * k], rest[2 * k + 1]]) % 1024;
    let m = &rest[2 * k + 2..];
    let expected = match variant {
        KeccakVariant::Sha3_224 => sha3::Sha3_224::digest(m).to_vec(),
        KeccakVariant::Sha3_256 => sha3::Sha3_256::digest(m).to_vec(),
        KeccakVariant::Sha3_384 => sha3::Sha3_384::digest(m).to_vec(),
        KeccakVariant::Sha3_512 => sha3::Sha3_512::digest(m).to_vec(),
        KeccakVariant::Shake128 => xof::<sha3::Shake128>(m, d as usize),
        KeccakVariant::Shake256 => xof::<sha3::Shake256>(m, d as usize),
        KeccakVariant::Keccak256 => sha3::Keccak256::digest(m).to_vec(),
    };
    assert_eq!(hash_lean::keccak_stream(variant, &pieces, m, d), expected, "{variant:?} in {pieces:?}");
});
