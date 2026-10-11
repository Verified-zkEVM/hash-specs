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
