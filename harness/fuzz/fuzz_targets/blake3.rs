//! Coverage-guided fuzzing of BLAKE3 in all three modes against the official `blake3` crate.
//!
//! Input layout: a mode byte, a big-endian 16-bit output length, a 32-byte key (or, for
//! `derive_key`, a context-length byte and the context), then the message.

#![no_main]

use hash_lean::Blake3Mode;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Some((&[mode, n0, n1], rest)) = data.split_first_chunk::<3>() else { return };
    let n = u16::from_be_bytes([n0, n1]) as usize % 1100;
    let (mode, m, mut h) = match mode % 3 {
        0 => (Blake3Mode::Hash, rest, blake3::Hasher::new()),
        1 => {
            let Some((key, m)) = rest.split_first_chunk::<32>() else { return };
            (Blake3Mode::Keyed(key), m, blake3::Hasher::new_keyed(key))
        }
        _ => {
            let Some((&cl, rest)) = rest.split_first() else { return };
            let cl = cl as usize % 64;
            if rest.len() < cl {
                return;
            }
            let (context, m) = rest.split_at(cl);
            let Ok(context_str) = std::str::from_utf8(context) else { return };
            (Blake3Mode::DeriveKey(context), m, blake3::Hasher::new_derive_key(context_str))
        }
    };
    h.update(m);
    let mut expected = vec![0u8; n];
    h.finalize_xof().fill(&mut expected);
    assert_eq!(hash_lean::blake3(mode, m, n), expected, "{mode:?}");
});
