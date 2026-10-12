//! Coverage-guided fuzzing of BLAKE2b and BLAKE2s against `blake2b_simd` and `blake2s_simd`,
//! with fuzzer-chosen output length, key, salt and personalisation.
//!
//! Input layout: four bytes choosing the output length and the key, salt and personalisation
//! lengths, then those parameters, then the message.

#![no_main]

use hash_lean::Blake2Params;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Some((&[nn, kk, sl, pl], rest)) = data.split_first_chunk::<4>() else { return };
    let (kk, sl, pl) = (kk as usize % 65, sl as usize % 17, pl as usize % 17);
    if rest.len() < kk + sl + pl {
        return;
    }
    let (key, rest) = rest.split_at(kk);
    let (salt, rest) = rest.split_at(sl);
    let (personal, m) = rest.split_at(pl);

    let p = Blake2Params { out_len: nn % 64 + 1, key, salt, personal };
    let expected = blake2b_simd::Params::new()
        .hash_length(p.out_len as usize)
        .key(key)
        .salt(salt)
        .personal(personal)
        .hash(m);
    assert_eq!(hash_lean::blake2b(&p, m), expected.as_bytes(), "BLAKE2b, {p:?}");

    let p = Blake2Params {
        out_len: nn % 32 + 1,
        key: &key[..kk.min(32)],
        salt: &salt[..sl.min(8)],
        personal: &personal[..pl.min(8)],
    };
    let expected = blake2s_simd::Params::new()
        .hash_length(p.out_len as usize)
        .key(p.key)
        .salt(p.salt)
        .personal(p.personal)
        .hash(m);
    assert_eq!(hash_lean::blake2s(&p, m), expected.as_bytes(), "BLAKE2s, {p:?}");
});
