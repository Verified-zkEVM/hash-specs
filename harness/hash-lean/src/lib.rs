//! In-process bindings to the fast Lean specifications of the `Hash` library.
//!
//! The Lean functions are compiled by Lake into a static library and exported under C names
//! (see `HashFFI/Export.lean`). This crate links that library together with the Lean runtime
//! and exposes each hash as a safe Rust function on byte slices. It exists for differential
//! testing against independent implementations, and for benchmarking.

use std::cell::Cell;
use std::sync::Once;

#[allow(non_camel_case_types)]
type lean_object = std::ffi::c_void;
type LeanFn = unsafe extern "C" fn(*mut lean_object) -> *mut lean_object;

extern "C" {
    fn hs_init() -> i32;
    fn hs_init_thread();
    fn hs_call_bytes(f: LeanFn, input: *const u8, len: usize, out: *mut u8, cap: usize) -> usize;

    fn hs_sha224(m: *mut lean_object) -> *mut lean_object;
    fn hs_sha256(m: *mut lean_object) -> *mut lean_object;
    fn hs_sha384(m: *mut lean_object) -> *mut lean_object;
    fn hs_sha512(m: *mut lean_object) -> *mut lean_object;
    fn hs_sha512t224(m: *mut lean_object) -> *mut lean_object;
    fn hs_sha512t256(m: *mut lean_object) -> *mut lean_object;
    fn hs_sha2_stream(input: *mut lean_object) -> *mut lean_object;
    fn hs_sha3x224(m: *mut lean_object) -> *mut lean_object;
    fn hs_sha3x256(m: *mut lean_object) -> *mut lean_object;
    fn hs_sha3x384(m: *mut lean_object) -> *mut lean_object;
    fn hs_sha3x512(m: *mut lean_object) -> *mut lean_object;
    fn hs_keccak256(m: *mut lean_object) -> *mut lean_object;
    fn hs_shake128(input: *mut lean_object) -> *mut lean_object;
    fn hs_shake256(input: *mut lean_object) -> *mut lean_object;
    fn hs_keccak_stream(input: *mut lean_object) -> *mut lean_object;
    fn hs_blake2b(input: *mut lean_object) -> *mut lean_object;
    fn hs_blake2s(input: *mut lean_object) -> *mut lean_object;
    fn hs_blake2b_f(input: *mut lean_object) -> *mut lean_object;
    fn hs_blake2_stream(input: *mut lean_object) -> *mut lean_object;
    fn hs_blake3(input: *mut lean_object) -> *mut lean_object;
    fn hs_blake3_stream(input: *mut lean_object) -> *mut lean_object;
    fn hs_poseidon_circom(input: *mut lean_object) -> *mut lean_object;
    fn hs_poseidon2(input: *mut lean_object) -> *mut lean_object;
    fn hs_poseidon2_sponge(input: *mut lean_object) -> *mut lean_object;
    fn hs_poseidon2_compress(input: *mut lean_object) -> *mut lean_object;
}

static INIT: Once = Once::new();

thread_local! {
    static THREAD_READY: Cell<bool> = const { Cell::new(false) };
}

/// Make sure the Lean runtime is initialized, and that the current thread may call into it.
fn ensure_ready() {
    if THREAD_READY.with(Cell::get) {
        return;
    }
    let mut initialized_here = false;
    INIT.call_once(|| {
        // SAFETY: called exactly once, before any other call into Lean.
        let rc = unsafe { hs_init() };
        assert_eq!(rc, 0, "Lean module initialization failed");
        initialized_here = true;
    });
    if !initialized_here {
        // SAFETY: the runtime is initialized; this thread has not been set up yet.
        unsafe { hs_init_thread() };
    }
    THREAD_READY.with(|r| r.set(true));
}

/// Call an exported Lean function of type `ByteArray → ByteArray`.
fn call(f: LeanFn, input: &[u8], expected_len: usize) -> Vec<u8> {
    ensure_ready();
    let mut out = vec![0u8; expected_len];
    // SAFETY: `input` and `out` are valid for the given lengths; `f` is an exported Lean
    // function taking and returning a `ByteArray`.
    let n = unsafe { hs_call_bytes(f, input.as_ptr(), input.len(), out.as_mut_ptr(), out.len()) };
    if n > out.len() {
        out.resize(n, 0);
        // SAFETY: as above, with a buffer large enough for the whole result.
        unsafe { hs_call_bytes(f, input.as_ptr(), input.len(), out.as_mut_ptr(), out.len()) };
    }
    out.truncate(n);
    out
}

/// SHA-224, computed by the Lean fast specification.
pub fn sha224(m: &[u8]) -> Vec<u8> {
    call(hs_sha224, m, 28)
}

/// SHA-256, computed by the Lean fast specification.
pub fn sha256(m: &[u8]) -> Vec<u8> {
    call(hs_sha256, m, 32)
}

/// SHA-384, computed by the Lean fast specification.
pub fn sha384(m: &[u8]) -> Vec<u8> {
    call(hs_sha384, m, 48)
}

/// SHA-512, computed by the Lean fast specification.
pub fn sha512(m: &[u8]) -> Vec<u8> {
    call(hs_sha512, m, 64)
}

/// SHA-512/224, computed by the Lean fast specification.
pub fn sha512_224(m: &[u8]) -> Vec<u8> {
    call(hs_sha512t224, m, 28)
}

/// SHA-512/256, computed by the Lean fast specification.
pub fn sha512_256(m: &[u8]) -> Vec<u8> {
    call(hs_sha512t256, m, 32)
}

/// A SHA-2 variant, for the streaming interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sha2Variant {
    Sha224 = 0,
    Sha256 = 1,
    Sha384 = 2,
    Sha512 = 3,
    Sha512_224 = 4,
    Sha512_256 = 5,
}

impl Sha2Variant {
    /// All variants.
    pub const ALL: [Sha2Variant; 6] = [
        Sha2Variant::Sha224,
        Sha2Variant::Sha256,
        Sha2Variant::Sha384,
        Sha2Variant::Sha512,
        Sha2Variant::Sha512_224,
        Sha2Variant::Sha512_256,
    ];

    /// The digest length in bytes.
    pub fn digest_len(self) -> usize {
        match self {
            Sha2Variant::Sha224 | Sha2Variant::Sha512_224 => 28,
            Sha2Variant::Sha256 | Sha2Variant::Sha512_256 => 32,
            Sha2Variant::Sha384 => 48,
            Sha2Variant::Sha512 => 64,
        }
    }
}

/// Hash `m` with the Lean streaming interface, absorbing it in pieces whose sizes cycle through
/// `pieces` (a size of 0 is an empty update; at most 255 sizes are used).
pub fn sha2_stream(variant: Sha2Variant, pieces: &[u16], m: &[u8]) -> Vec<u8> {
    let pieces = &pieces[..pieces.len().min(255)];
    let mut input = Vec::with_capacity(2 + 2 * pieces.len() + m.len());
    input.push(variant as u8);
    input.push(pieces.len() as u8);
    for p in pieces {
        input.extend_from_slice(&p.to_be_bytes());
    }
    input.extend_from_slice(m);
    call(hs_sha2_stream, &input, variant.digest_len())
}

/// SHA3-224, computed by the Lean fast specification.
pub fn sha3_224(m: &[u8]) -> Vec<u8> {
    call(hs_sha3x224, m, 28)
}

/// SHA3-256, computed by the Lean fast specification.
pub fn sha3_256(m: &[u8]) -> Vec<u8> {
    call(hs_sha3x256, m, 32)
}

/// SHA3-384, computed by the Lean fast specification.
pub fn sha3_384(m: &[u8]) -> Vec<u8> {
    call(hs_sha3x384, m, 48)
}

/// SHA3-512, computed by the Lean fast specification.
pub fn sha3_512(m: &[u8]) -> Vec<u8> {
    call(hs_sha3x512, m, 64)
}

/// Ethereum's Keccak-256, computed by the Lean fast specification.
pub fn keccak256(m: &[u8]) -> Vec<u8> {
    call(hs_keccak256, m, 32)
}

fn xof(f: LeanFn, m: &[u8], out_len: usize) -> Vec<u8> {
    let len = u32::try_from(out_len).expect("output length fits in 32 bits");
    let mut input = Vec::with_capacity(4 + m.len());
    input.extend_from_slice(&len.to_be_bytes());
    input.extend_from_slice(m);
    call(f, &input, out_len)
}

/// SHAKE128 with `out_len` bytes of output, computed by the Lean fast specification.
pub fn shake128(m: &[u8], out_len: usize) -> Vec<u8> {
    xof(hs_shake128, m, out_len)
}

/// SHAKE256 with `out_len` bytes of output, computed by the Lean fast specification.
pub fn shake256(m: &[u8], out_len: usize) -> Vec<u8> {
    xof(hs_shake256, m, out_len)
}

/// A Keccak-based function, for the streaming interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeccakVariant {
    Sha3_224 = 0,
    Sha3_256 = 1,
    Sha3_384 = 2,
    Sha3_512 = 3,
    Shake128 = 4,
    Shake256 = 5,
    Keccak256 = 6,
}

impl KeccakVariant {
    /// All variants.
    pub const ALL: [KeccakVariant; 7] = [
        KeccakVariant::Sha3_224,
        KeccakVariant::Sha3_256,
        KeccakVariant::Sha3_384,
        KeccakVariant::Sha3_512,
        KeccakVariant::Shake128,
        KeccakVariant::Shake256,
        KeccakVariant::Keccak256,
    ];

    /// The output length in bytes, where `xof_len` is used by SHAKE.
    pub fn output_len(self, xof_len: u16) -> usize {
        match self {
            KeccakVariant::Sha3_224 => 28,
            KeccakVariant::Sha3_256 | KeccakVariant::Keccak256 => 32,
            KeccakVariant::Sha3_384 => 48,
            KeccakVariant::Sha3_512 => 64,
            KeccakVariant::Shake128 | KeccakVariant::Shake256 => xof_len as usize,
        }
    }
}

/// Hash `m` with the Lean Keccak streaming interface, absorbing it in pieces whose sizes cycle
/// through `pieces` (a size of 0 is an empty update; at most 255 sizes are used). SHAKE
/// produces `xof_len` bytes.
pub fn keccak_stream(variant: KeccakVariant, pieces: &[u16], m: &[u8], xof_len: u16) -> Vec<u8> {
    let pieces = &pieces[..pieces.len().min(255)];
    let mut input = Vec::with_capacity(4 + 2 * pieces.len() + m.len());
    input.push(variant as u8);
    input.push(pieces.len() as u8);
    for p in pieces {
        input.extend_from_slice(&p.to_be_bytes());
    }
    input.extend_from_slice(&xof_len.to_be_bytes());
    input.extend_from_slice(m);
    call(hs_keccak_stream, &input, variant.output_len(xof_len))
}

/// The parameters of a BLAKE2 computation: the output length in bytes, and the key, salt and
/// personalisation (each possibly empty).
#[derive(Clone, Copy, Debug)]
pub struct Blake2Params<'a> {
    pub out_len: u8,
    pub key: &'a [u8],
    pub salt: &'a [u8],
    pub personal: &'a [u8],
}

impl Blake2Params<'_> {
    fn encode(&self, input: &mut Vec<u8>, m: &[u8]) {
        let len = |b: &[u8]| u8::try_from(b.len()).expect("parameter fits in 255 bytes");
        input.extend_from_slice(&[self.out_len, len(self.key), len(self.salt), len(self.personal)]);
        input.extend_from_slice(self.key);
        input.extend_from_slice(self.salt);
        input.extend_from_slice(self.personal);
        input.extend_from_slice(m);
    }
}

fn blake2(f: LeanFn, params: &Blake2Params, m: &[u8]) -> Vec<u8> {
    let mut input = Vec::with_capacity(4 + m.len() + 64);
    params.encode(&mut input, m);
    call(f, &input, params.out_len as usize)
}

/// BLAKE2b with the given parameters, computed by the Lean fast specification.
pub fn blake2b(params: &Blake2Params, m: &[u8]) -> Vec<u8> {
    blake2(hs_blake2b, params, m)
}

/// BLAKE2s with the given parameters, computed by the Lean fast specification.
pub fn blake2s(params: &Blake2Params, m: &[u8]) -> Vec<u8> {
    blake2(hs_blake2s, params, m)
}

/// The EIP-152 BLAKE2b `F` precompile on a raw input, computed by the Lean fast specification:
/// `None` if the input is invalid.
pub fn blake2b_f(input: &[u8]) -> Option<Vec<u8>> {
    let out = call(hs_blake2b_f, input, 64);
    (!out.is_empty()).then_some(out)
}

/// A BLAKE2 variant, for the streaming interface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Blake2Variant {
    Blake2b = 0,
    Blake2s = 1,
}

/// Hash `m` with the Lean BLAKE2 streaming interface, adding it in pieces whose sizes cycle
/// through `pieces` (a size of 0 is an empty update; at most 255 sizes are used).
pub fn blake2_stream(
    variant: Blake2Variant,
    params: &Blake2Params,
    pieces: &[u16],
    m: &[u8],
) -> Vec<u8> {
    let pieces = &pieces[..pieces.len().min(255)];
    let mut input = Vec::with_capacity(6 + 2 * pieces.len() + m.len() + 64);
    input.push(variant as u8);
    input.push(pieces.len() as u8);
    for p in pieces {
        input.extend_from_slice(&p.to_be_bytes());
    }
    params.encode(&mut input, m);
    call(hs_blake2_stream, &input, params.out_len as usize)
}

/// A BLAKE3 mode, with its key or context string.
#[derive(Clone, Copy, Debug)]
pub enum Blake3Mode<'a> {
    /// The `hash` mode.
    Hash,
    /// The `keyed_hash` mode with a 32-byte key.
    Keyed(&'a [u8; 32]),
    /// The `derive_key` mode with a context string.
    DeriveKey(&'a [u8]),
}

impl Blake3Mode<'_> {
    fn encode(&self, input: &mut Vec<u8>, out_len: usize, m: &[u8]) {
        let (mode, k): (u8, &[u8]) = match self {
            Blake3Mode::Hash => (0, &[]),
            Blake3Mode::Keyed(key) => (1, &key[..]),
            Blake3Mode::DeriveKey(context) => (2, context),
        };
        input.push(mode);
        input.extend_from_slice(&u32::try_from(out_len).expect("output length fits").to_be_bytes());
        input.extend_from_slice(&u16::try_from(k.len()).expect("context fits").to_be_bytes());
        input.extend_from_slice(k);
        input.extend_from_slice(m);
    }
}

/// BLAKE3 in the given mode with `out_len` bytes of output, computed by the Lean fast
/// specification.
pub fn blake3(mode: Blake3Mode, m: &[u8], out_len: usize) -> Vec<u8> {
    let mut input = Vec::with_capacity(7 + m.len() + 64);
    mode.encode(&mut input, out_len, m);
    call(hs_blake3, &input, out_len)
}

/// BLAKE3 with the Lean streaming interface, adding `m` in pieces whose sizes cycle through
/// `pieces` (a size of 0 is an empty update; at most 255 sizes are used).
pub fn blake3_stream(mode: Blake3Mode, pieces: &[u16], m: &[u8], out_len: usize) -> Vec<u8> {
    let pieces = &pieces[..pieces.len().min(255)];
    let mut input = Vec::with_capacity(8 + 2 * pieces.len() + m.len() + 64);
    input.push(pieces.len() as u8);
    for p in pieces {
        input.extend_from_slice(&p.to_be_bytes());
    }
    mode.encode(&mut input, out_len, m);
    call(hs_blake3_stream, &input, out_len)
}

/// circomlib's Poseidon over the BN254 scalar field, computed by the Lean fast specification on
/// raw Montgomery limbs. The inputs and the output are 32-byte big-endian integers; the inputs
/// are reduced modulo the field order. Returns `None` unless there are 1 to 16 inputs.
pub fn poseidon_circom(inputs: &[[u8; 32]]) -> Option<[u8; 32]> {
    let input: Vec<u8> = inputs.concat();
    let out = call(hs_poseidon_circom, &input, 32);
    out.try_into().ok()
}

/// A Poseidon2 instance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Poseidon2Instance {
    /// Plonky3's BabyBear, width 16.
    BabyBear16 = 0,
    /// Plonky3's BabyBear, width 24.
    BabyBear24 = 1,
    /// Plonky3's KoalaBear, width 16.
    KoalaBear16 = 2,
    /// Plonky3's KoalaBear, width 24.
    KoalaBear24 = 3,
    /// HorizenLabs' BN254, width 3.
    HorizenLabsBn254 = 4,
}

impl Poseidon2Instance {
    /// The width and the size of an element in bytes.
    pub fn shape(self) -> (usize, usize) {
        match self {
            Poseidon2Instance::BabyBear16 | Poseidon2Instance::KoalaBear16 => (16, 4),
            Poseidon2Instance::BabyBear24 | Poseidon2Instance::KoalaBear24 => (24, 4),
            Poseidon2Instance::HorizenLabsBn254 => (3, 32),
        }
    }
}

/// A Poseidon2 permutation, computed by the Lean fast specification. The state is the
/// concatenation of big-endian elements (4 bytes for the 31-bit fields, 32 bytes for BN254),
/// reduced modulo the field order. Returns `None` if the state has the wrong length.
pub fn poseidon2(instance: Poseidon2Instance, state: &[u8]) -> Option<Vec<u8>> {
    let (t, k) = instance.shape();
    let mut input = vec![instance as u8];
    input.extend_from_slice(state);
    let out = call(hs_poseidon2, &input, t * k);
    (out.len() == t * k).then_some(out)
}

fn words_to_bytes(xs: &[u32]) -> Vec<u8> {
    xs.iter().flat_map(|x| x.to_be_bytes()).collect()
}

fn bytes_to_words(bs: &[u8]) -> Vec<u32> {
    bs.as_chunks::<4>().0.iter().map(|c| u32::from_be_bytes(*c)).collect()
}

/// Plonky3's padding-free sponge over a 31-bit Poseidon2 instance, computed by the Lean fast
/// specification. Returns `None` for the BN254 instance or parameters outside Plonky3's bounds
/// (`0 < rate < width`, `0 < out <= rate`).
pub fn poseidon2_sponge(
    instance: Poseidon2Instance,
    rate: u8,
    out: u8,
    xs: &[u32],
) -> Option<Vec<u32>> {
    let mut input = vec![instance as u8, rate, out];
    input.extend(words_to_bytes(xs));
    let res = call(hs_poseidon2_sponge, &input, 4 * out as usize);
    (!res.is_empty()).then(|| bytes_to_words(&res))
}

/// Plonky3's truncated-permutation compression over a 31-bit Poseidon2 instance, computed by the
/// Lean fast specification: the chunks of `chunk` elements in `xs` are placed at the start of
/// the zero state, and the first `chunk` elements of its permutation are returned.
pub fn poseidon2_compress(instance: Poseidon2Instance, chunk: u8, xs: &[u32]) -> Option<Vec<u32>> {
    let mut input = vec![instance as u8, chunk];
    input.extend(words_to_bytes(xs));
    let res = call(hs_poseidon2_compress, &input, 4 * chunk as usize);
    (!res.is_empty()).then(|| bytes_to_words(&res))
}
