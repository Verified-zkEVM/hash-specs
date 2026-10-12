//! Coverage-guided fuzzing of circomlib's Poseidon over BN254 against `poseidon-rs` (all 16
//! widths) and `light-poseidon` (up to 12 inputs).
//!
//! Input layout: 1 to 16 big-endian 32-byte integers, reduced modulo the field order; trailing
//! bytes are ignored.

#![no_main]

use ark_ff::{BigInteger, PrimeField};
use libfuzzer_sys::fuzz_target;
use light_poseidon::{Poseidon, PoseidonHasher};

fuzz_target!(|data: &[u8]| {
    let inputs: Vec<[u8; 32]> = data.as_chunks::<32>().0.iter().take(16).copied().collect();
    if inputs.is_empty() {
        return;
    }
    let xs: Vec<ark_bn254::Fr> =
        inputs.iter().map(|b| ark_bn254::Fr::from_be_bytes_mod_order(b)).collect();
    let got = hash_lean::poseidon_circom(&inputs).expect("1 to 16 inputs");

    let ys: Vec<poseidon_rs::Fr> = xs
        .iter()
        .map(|x| {
            <poseidon_rs::Fr as ff::PrimeField>::from_str(&x.into_bigint().to_string()).unwrap()
        })
        .collect();
    let expected = hex::decode(ff::to_hex(&poseidon_rs::Poseidon::new().hash(ys).unwrap()));
    assert_eq!(got.to_vec(), expected.unwrap(), "poseidon-rs, {} inputs", inputs.len());

    if inputs.len() <= 12 {
        let mut h = Poseidon::<ark_bn254::Fr>::new_circom(inputs.len()).unwrap();
        let expected = h.hash(&xs).unwrap().into_bigint().to_bytes_be();
        assert_eq!(got.to_vec(), expected, "light-poseidon, {} inputs", inputs.len());
    }
});
