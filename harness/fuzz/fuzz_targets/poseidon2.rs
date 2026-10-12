//! Coverage-guided fuzzing of Poseidon2 against Plonky3 (BabyBear and KoalaBear, widths 16 and
//! 24) and HorizenLabs' reference implementation `zkhash` (BN254, width 3).
//!
//! Input layout: an instance byte (0–3 for BabyBear 16 and 24 and KoalaBear 16 and 24, otherwise
//! BN254), then the state: big-endian elements of 4 bytes (31-bit fields) or 32 bytes (BN254),
//! reduced modulo the field order. Short inputs are padded with zeros.

#![no_main]

use hash_lean::Poseidon2Instance;
use libfuzzer_sys::fuzz_target;
use p3_field::PrimeField32;
use p3_symmetric::Permutation;

macro_rules! plonky3 {
    ($field:ty, $p:expr, $width:literal, $perm:path, $state:expr) => {{
        let mut s: [$field; $width] = core::array::from_fn(|i| {
            let w = u32::from_be_bytes($state[4 * i..4 * i + 4].try_into().unwrap());
            <$field>::new(w % $p)
        });
        $perm().permute_mut(&mut s);
        s.iter().flat_map(|x| x.as_canonical_u32().to_be_bytes()).collect::<Vec<u8>>()
    }};
}

fuzz_target!(|data: &[u8]| {
    let Some((&tag, rest)) = data.split_first() else { return };
    let instance = match tag {
        0 => Poseidon2Instance::BabyBear16,
        1 => Poseidon2Instance::BabyBear24,
        2 => Poseidon2Instance::KoalaBear16,
        3 => Poseidon2Instance::KoalaBear24,
        _ => Poseidon2Instance::HorizenLabsBn254,
    };
    let (t, k) = instance.shape();
    let mut state = rest[..rest.len().min(t * k)].to_vec();
    state.resize(t * k, 0);
    let got = hash_lean::poseidon2(instance, &state).expect("state length");
    let expected = match instance {
        Poseidon2Instance::BabyBear16 => plonky3!(
            p3_baby_bear::BabyBear,
            0x7800_0001,
            16,
            p3_baby_bear::default_babybear_poseidon2_16,
            state
        ),
        Poseidon2Instance::BabyBear24 => plonky3!(
            p3_baby_bear::BabyBear,
            0x7800_0001,
            24,
            p3_baby_bear::default_babybear_poseidon2_24,
            state
        ),
        Poseidon2Instance::KoalaBear16 => plonky3!(
            p3_koala_bear::KoalaBear,
            0x7f00_0001,
            16,
            p3_koala_bear::default_koalabear_poseidon2_16,
            state
        ),
        Poseidon2Instance::KoalaBear24 => plonky3!(
            p3_koala_bear::KoalaBear,
            0x7f00_0001,
            24,
            p3_koala_bear::default_koalabear_poseidon2_24,
            state
        ),
        Poseidon2Instance::HorizenLabsBn254 => {
            use zkhash::ark_ff::{BigInteger, PrimeField};
            use zkhash::fields::bn256::FpBN256;
            use zkhash::poseidon2::poseidon2::Poseidon2;
            use zkhash::poseidon2::poseidon2_instance_bn256::POSEIDON2_BN256_PARAMS;
            let xs: Vec<FpBN256> = state
                .as_chunks::<32>()
                .0
                .iter()
                .map(|c| FpBN256::from_be_bytes_mod_order(c))
                .collect();
            let out = Poseidon2::new(&POSEIDON2_BN256_PARAMS).permutation(&xs);
            out.iter().flat_map(|x| x.into_bigint().to_bytes_be()).collect()
        }
    };
    assert_eq!(got, expected, "{instance:?}");
});
