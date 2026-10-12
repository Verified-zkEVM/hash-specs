//! Differential tests: the Lean fast specification of circomlib's Poseidon over BN254 against
//! `light-poseidon` (Light Protocol, audited; up to 12 inputs) and `poseidon-rs` (iden3's port of
//! circomlib's constants; up to 16 inputs).

use ark_ff::{BigInteger, PrimeField};
use light_poseidon::{Poseidon, PoseidonHasher};
use proptest::prelude::*;

/// The inputs reduced modulo the field order, as `light-poseidon`'s field elements.
fn ark_inputs(inputs: &[[u8; 32]]) -> Vec<ark_bn254::Fr> {
    inputs.iter().map(|b| ark_bn254::Fr::from_be_bytes_mod_order(b)).collect()
}

fn light(inputs: &[[u8; 32]]) -> [u8; 32] {
    let mut h = Poseidon::<ark_bn254::Fr>::new_circom(inputs.len()).expect("width");
    let out = h.hash(&ark_inputs(inputs)).expect("hash");
    out.into_bigint().to_bytes_be().try_into().expect("32 bytes")
}

fn iden3(inputs: &[[u8; 32]]) -> [u8; 32] {
    use ff::PrimeField as _;
    let xs: Vec<poseidon_rs::Fr> = ark_inputs(inputs)
        .iter()
        .map(|x| poseidon_rs::Fr::from_str(&x.into_bigint().to_string()).expect("decimal"))
        .collect();
    let out = poseidon_rs::Poseidon::new().hash(xs).expect("hash");
    hex::decode(ff::to_hex(&out)).expect("hex").try_into().expect("32 bytes")
}

fn lean(inputs: &[[u8; 32]]) -> [u8; 32] {
    hash_lean::poseidon_circom(inputs).expect("1 to 16 inputs")
}

fn check(inputs: &[[u8; 32]]) {
    let got = lean(inputs);
    assert_eq!(got, iden3(inputs), "poseidon-rs, {} inputs", inputs.len());
    if inputs.len() <= 12 {
        assert_eq!(got, light(inputs), "light-poseidon, {} inputs", inputs.len());
    }
}

fn int(n: u64) -> [u8; 32] {
    let mut b = [0u8; 32];
    b[24..].copy_from_slice(&n.to_be_bytes());
    b
}

#[test]
fn known_answer() {
    // circomlib's `poseidon([1, 2])`, from its test suite.
    let expected =
        hex::decode("115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a").unwrap();
    assert_eq!(lean(&[int(1), int(2)]).to_vec(), expected);
}

#[test]
fn every_width() {
    for n in 1..=16u64 {
        let inputs: Vec<[u8; 32]> = (1..=n).map(int).collect();
        check(&inputs);
    }
}

#[test]
fn edge_values() {
    // 0, p − 1, p, and 2²⁵⁶ − 1 (the last two are reduced modulo p).
    let p_minus_1 =
        hex::decode("30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000").unwrap();
    let p =
        hex::decode("30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001").unwrap();
    let edges = [int(0), p_minus_1.try_into().unwrap(), p.try_into().unwrap(), [0xff; 32]];
    for a in edges {
        for b in edges {
            check(&[a, b]);
        }
    }
}

#[test]
fn malformed_input() {
    assert_eq!(hash_lean::poseidon_circom(&[]), None);
    assert_eq!(hash_lean::poseidon_circom(&[int(1); 17]), None);
}

proptest! {
    #[test]
    fn random_inputs(inputs in prop::collection::vec(any::<[u8; 32]>(), 1..=16)) {
        check(&inputs);
    }
}
