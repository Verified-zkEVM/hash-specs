//! Builds the Lean static libraries with Lake and links them, together with the Lean runtime and
//! CompPoly's zero-import Montgomery arithmetic, into this crate.
//!
//! Set `HASH_LEAN_SKIP_LAKE=1` to skip the `lake build` step (for example in CI, after building
//! the Lean libraries in an earlier step).

use std::{env, path::PathBuf, process::Command};

/// The Lake target building CompPoly's zero-import Montgomery arithmetic, which `HashZK.Raw` uses.
const COMPPOLY_FACET: &str = "+CompPoly.Fields.Montgomery.Native64x8Defs:o";
/// The object file it produces.
/// The `zk` package shares the core package's dependency checkouts (`packagesDir`).
const COMPPOLY_OBJECT: &str =
    ".lake/packages/CompPoly/.lake/build/ir/CompPoly/Fields/Montgomery/Native64x8Defs.c.o.export";

fn main() {
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let root = manifest.join("../..").canonicalize().expect("repository root");
    // The Lean libraries are built from the `zk` package, which depends on the core package in
    // the repository root; Lake builds each package's libraries in its own `.lake/build`.
    let zk = root.join("zk");

    if env::var_os("HASH_LEAN_SKIP_LAKE").is_none() {
        let status = Command::new("lake")
            .args(["build", "HashFFI:static", "Hash:static", "HashZK:static", COMPPOLY_FACET])
            .current_dir(&zk)
            .status()
            .expect("failed to run `lake`; is elan installed?");
        assert!(status.success(), "`lake build` failed");
    }

    let output = Command::new("lean")
        .arg("--print-prefix")
        .current_dir(&root)
        .output()
        .expect("failed to run `lean --print-prefix`");
    let prefix = PathBuf::from(String::from_utf8(output.stdout).unwrap().trim());

    cc::Build::new()
        .file("csrc/shim.c")
        .include(prefix.join("include"))
        .opt_level(2)
        .compile("hash_lean_shim");

    println!("cargo:rustc-link-search=native={}", zk.join(".lake/build/lib").display());
    println!("cargo:rustc-link-search=native={}", root.join(".lake/build/lib").display());
    println!("cargo:rustc-link-search=native={}", prefix.join("lib/lean").display());
    println!("cargo:rustc-link-search=native={}", prefix.join("lib").display());

    // CompPoly's runtime arithmetic is built as a single object file; archive it.
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    let comppoly = root.join(COMPPOLY_OBJECT);
    assert!(comppoly.exists(), "{} not found", comppoly.display());
    let _ = std::fs::remove_file(out.join("libhash_comppoly.a"));
    let status = Command::new("ar")
        .arg("rcs")
        .arg(out.join("libhash_comppoly.a"))
        .arg(&comppoly)
        .status()
        .expect("failed to run `ar`");
    assert!(status.success(), "`ar rcs` failed");
    println!("cargo:rustc-link-search=native={}", out.display());

    let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap();
    let lean_libs = [
        "hash_x2dspecs_x2dzk_HashFFI",
        "hash_x2dspecs_x2dzk_HashZK",
        "hash_x2dspecs_Hash",
        "hash_comppoly",
        "Init",
        "leanrt",
        "uv",
        "gmp",
    ];
    if target_os == "linux" {
        // The Lean archives refer to each other, and GNU ld scans each archive once, so merge
        // them into a single archive, within which it resolves references in any order. The Lean
        // runtime is built against the static libc++ shipped in the toolchain's `lib`, not the
        // system's libstdc++.
        let dirs = [
            zk.join(".lake/build/lib"),
            root.join(".lake/build/lib"),
            out.clone(),
            prefix.join("lib/lean"),
            prefix.join("lib"),
        ];
        let mut script = format!("CREATE {}\n", out.join("libhash_lean_all.a").display());
        for lib in lean_libs.iter().chain(&["c++", "c++abi"]) {
            let file = format!("lib{lib}.a");
            let path = dirs.iter().map(|d| d.join(&file)).find(|p| p.exists());
            let path = path.unwrap_or_else(|| panic!("{file} not found"));
            script += &format!("ADDLIB {}\n", path.display());
        }
        script += "SAVE\nEND\n";
        let mut ar = Command::new("ar")
            .arg("-M")
            .stdin(std::process::Stdio::piped())
            .spawn()
            .expect("failed to run `ar`");
        std::io::Write::write_all(ar.stdin.as_mut().unwrap(), script.as_bytes()).unwrap();
        assert!(ar.wait().unwrap().success(), "`ar -M` failed");
        println!("cargo:rustc-link-lib=static=hash_lean_all");
        for lib in ["m", "pthread", "dl"] {
            println!("cargo:rustc-link-lib=dylib={lib}");
        }
    } else {
        for lib in lean_libs {
            println!("cargo:rustc-link-lib=static={lib}");
        }
        println!("cargo:rustc-link-lib=dylib=c++");
    }

    for dir in [
        "Hash",
        "Hash.lean",
        "lakefile.toml",
        "lean-toolchain",
        "zk/HashFFI",
        "zk/HashZK",
        "zk/HashFFI.lean",
        "zk/HashZK.lean",
        "zk/lakefile.toml",
    ] {
        println!("cargo:rerun-if-changed={}", root.join(dir).display());
    }
    println!("cargo:rerun-if-changed=csrc/shim.c");
    println!("cargo:rerun-if-env-changed=HASH_LEAN_SKIP_LAKE");
}
