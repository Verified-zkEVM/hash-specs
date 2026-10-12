//! Coverage-guided fuzzing of the EIP-152 BLAKE2b `F` precompile against `revm-precompile`,
//! on raw inputs (valid or not). The round count is capped at 65535 to keep runs fast.

#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut input = data.to_vec();
    if input.len() >= 2 {
        input[0] = 0;
        input[1] = 0;
    }
    let expected = revm_precompile::blake2::run(&input, u64::MAX).ok().map(|o| o.bytes.to_vec());
    assert_eq!(hash_lean::blake2b_f(&input), expected);
});
