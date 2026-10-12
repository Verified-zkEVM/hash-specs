//! Differential tests: the Lean fast specification of Poseidon2 against Plonky3 0.8.0 for the
//! BabyBear and KoalaBear instances (its scalar code path, and its SIMD code path on the packed
//! field type), and against HorizenLabs' reference implementation (`zkhash`) and Plonky3's BN254
//! permutation (with `zkhash`'s constants) for the BN254 instance.
//!
//! Plonky3 and its forks are the only implementations of the BabyBear and KoalaBear instances, so
//! for those the two code paths of one implementation stand in for a second oracle.

use hash_lean::Poseidon2Instance;
use p3_field::{Field, PackedValue, PrimeField32};
use p3_symmetric::Permutation;
use proptest::prelude::*;

const BABY_BEAR: u32 = 0x7800_0001;
const KOALA_BEAR: u32 = 0x7f00_0001;

fn lean(instance: Poseidon2Instance, state: &[u8]) -> Vec<u8> {
    hash_lean::poseidon2(instance, state).expect("state length")
}

fn words(state: &[u8]) -> Vec<u32> {
    state.as_chunks::<4>().0.iter().map(|c| u32::from_be_bytes(*c)).collect()
}

fn bytes(xs: impl IntoIterator<Item = u32>) -> Vec<u8> {
    xs.into_iter().flat_map(u32::to_be_bytes).collect()
}

/// A Plonky3 31-bit permutation, by its scalar path and by its packed path (every lane holds a
/// different state; lane 0 is the given one).
macro_rules! plonky3 {
    ($name:ident, $field:ty, $p:expr, $width:literal, $perm:path) => {
        fn $name(state: &[u8]) -> (Vec<u8>, Vec<u8>) {
            let xs: Vec<$field> = words(state).iter().map(|&x| <$field>::new(x % $p)).collect();
            let perm = $perm();
            let mut scalar: [$field; $width] = xs.clone().try_into().unwrap();
            perm.permute_mut(&mut scalar);
            type P = <$field as Field>::Packing;
            let mut packed: [P; $width] = core::array::from_fn(|i| {
                P::from_fn(|lane| xs[i] + <$field>::new(((lane as u32) * (i as u32 + 1)) % $p))
            });
            perm.permute_mut(&mut packed);
            (
                bytes(scalar.iter().map(|x| x.as_canonical_u32())),
                bytes(packed.iter().map(|x| x.as_slice()[0].as_canonical_u32())),
            )
        }
    };
}

plonky3!(bb16, p3_baby_bear::BabyBear, BABY_BEAR, 16, p3_baby_bear::default_babybear_poseidon2_16);
plonky3!(bb24, p3_baby_bear::BabyBear, BABY_BEAR, 24, p3_baby_bear::default_babybear_poseidon2_24);
plonky3!(
    kb16,
    p3_koala_bear::KoalaBear,
    KOALA_BEAR,
    16,
    p3_koala_bear::default_koalabear_poseidon2_16
);
plonky3!(
    kb24,
    p3_koala_bear::KoalaBear,
    KOALA_BEAR,
    24,
    p3_koala_bear::default_koalabear_poseidon2_24
);

fn check31(instance: Poseidon2Instance, state: &[u8]) {
    let (scalar, packed) = match instance {
        Poseidon2Instance::BabyBear16 => bb16(state),
        Poseidon2Instance::BabyBear24 => bb24(state),
        Poseidon2Instance::KoalaBear16 => kb16(state),
        Poseidon2Instance::KoalaBear24 => kb24(state),
        Poseidon2Instance::HorizenLabsBn254 => unreachable!(),
    };
    let got = lean(instance, state);
    assert_eq!(got, scalar, "{instance:?}, Plonky3 scalar path");
    assert_eq!(got, packed, "{instance:?}, Plonky3 packed path");
}

/// HorizenLabs' reference implementation.
fn zkhash_bn254(state: &[u8]) -> Vec<u8> {
    use zkhash::ark_ff::{BigInteger, PrimeField};
    use zkhash::fields::bn256::FpBN256;
    use zkhash::poseidon2::poseidon2::Poseidon2;
    use zkhash::poseidon2::poseidon2_instance_bn256::POSEIDON2_BN256_PARAMS;
    let xs: Vec<FpBN256> =
        state.as_chunks::<32>().0.iter().map(|c| FpBN256::from_be_bytes_mod_order(c)).collect();
    let out = Poseidon2::new(&POSEIDON2_BN256_PARAMS).permutation(&xs);
    out.iter().flat_map(|x| x.into_bigint().to_bytes_be()).collect()
}

fn to_p3(x: zkhash::fields::bn256::FpBN256) -> p3_bn254::Bn254 {
    use zkhash::ark_ff::{BigInteger, PrimeField};
    let n = num_bigint::BigUint::from_bytes_be(&x.into_bigint().to_bytes_be());
    p3_bn254::Bn254::from_biguint(n).expect("canonical")
}

/// Plonky3's BN254 permutation, with the reference implementation's constants (it has none of
/// its own).
fn plonky3_bn254(state: &[u8]) -> Vec<u8> {
    use p3_field::PrimeField;
    use zkhash::ark_ff::PrimeField as _;
    use zkhash::fields::bn256::FpBN256;
    use zkhash::poseidon2::poseidon2_instance_bn256::RC3;
    let mut rc: Vec<[p3_bn254::Bn254; 3]> =
        RC3.iter().map(|r| core::array::from_fn(|i| to_p3(r[i]))).collect();
    let internal: Vec<p3_bn254::Bn254> = rc.drain(4..60).map(|r| r[0]).collect();
    let external = p3_poseidon2::ExternalLayerConstants::new(rc[..4].to_vec(), rc[4..].to_vec());
    let perm = p3_bn254::Poseidon2Bn254::<3>::new(external, internal);
    let mut s: [p3_bn254::Bn254; 3] = core::array::from_fn(|i| {
        to_p3(FpBN256::from_be_bytes_mod_order(&state[32 * i..32 * i + 32]))
    });
    perm.permute_mut(&mut s);
    s.iter()
        .flat_map(|x| {
            let b = x.as_canonical_biguint().to_bytes_be();
            let mut out = vec![0u8; 32 - b.len()];
            out.extend(b);
            out
        })
        .collect()
}

fn check_bn254(state: &[u8]) {
    let got = lean(Poseidon2Instance::HorizenLabsBn254, state);
    assert_eq!(got, zkhash_bn254(state), "zkhash");
    assert_eq!(got, plonky3_bn254(state), "Plonky3 BN254");
}

#[test]
fn known_answers() {
    // HorizenLabs' BN254 vector: the permutation of [0, 1, 2].
    let mut state = vec![0u8; 96];
    state[63] = 1;
    state[95] = 2;
    let expected = hex::decode(concat!(
        "0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033",
        "303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570",
        "1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8"
    ))
    .unwrap();
    assert_eq!(lean(Poseidon2Instance::HorizenLabsBn254, &state), expected);
    // Plonky3's KoalaBear width-16 vector.
    let input = [
        894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831, 120589055,
        19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920, 1783754913,
    ];
    let expected = [
        1934285469, 604889435, 133449501, 1026180808, 1830659359, 176667110, 1391183747, 351743874,
        1238264085, 1292768839, 2023573270, 1201586780, 1360691759, 1230682461, 748270449,
        651545025,
    ];
    assert_eq!(lean(Poseidon2Instance::KoalaBear16, &bytes(input)), bytes(expected));
}

#[test]
fn edge_states() {
    for (instance, p) in [
        (Poseidon2Instance::BabyBear16, BABY_BEAR),
        (Poseidon2Instance::BabyBear24, BABY_BEAR),
        (Poseidon2Instance::KoalaBear16, KOALA_BEAR),
        (Poseidon2Instance::KoalaBear24, KOALA_BEAR),
    ] {
        let t = instance.shape().0;
        for x in [0, 1, p - 1, p, u32::MAX] {
            check31(instance, &bytes(vec![x; t]));
        }
        check31(instance, &bytes((0..t as u32).collect::<Vec<_>>()));
    }
    let p_minus_1 =
        hex::decode("30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000000").unwrap();
    for x in [vec![0u8; 32], p_minus_1, vec![0xff; 32]] {
        check_bn254(&x.repeat(3));
    }
}

#[test]
fn malformed_input() {
    assert_eq!(hash_lean::poseidon2(Poseidon2Instance::BabyBear16, &[0; 63]), None);
    assert_eq!(hash_lean::poseidon2(Poseidon2Instance::HorizenLabsBn254, &[0; 95]), None);
}

proptest! {
    #[test]
    fn random_babybear16(s in prop::collection::vec(any::<u8>(), 64)) {
        check31(Poseidon2Instance::BabyBear16, &s);
    }

    #[test]
    fn random_babybear24(s in prop::collection::vec(any::<u8>(), 96)) {
        check31(Poseidon2Instance::BabyBear24, &s);
    }

    #[test]
    fn random_koalabear16(s in prop::collection::vec(any::<u8>(), 64)) {
        check31(Poseidon2Instance::KoalaBear16, &s);
    }

    #[test]
    fn random_koalabear24(s in prop::collection::vec(any::<u8>(), 96)) {
        check31(Poseidon2Instance::KoalaBear24, &s);
    }

    #[test]
    fn random_bn254(s in prop::collection::vec(any::<u8>(), 96)) {
        check_bn254(&s);
    }
}
