#!/usr/bin/env python3
"""Check the layering rules of ROADMAP.md §2.1.

1. Layer 1 (`Hash/`, `HashTests/`) imports only Lean core, Mathlib and Mathlib's own
   dependencies, and other Layer 1 modules. It never imports CompPoly or Layers 2 and 3.
2. The C-export library (`HashFFI`) is Mathlib-free: none of its transitive imports inside this
   repository or CompPoly import Mathlib, Batteries, Aesop, Qq, Plausible or `Hash.Init`. It is linked into the
   Rust harness as a static library, and must stay small.
3. Layer 1 contains no `sorry`, `admit`, `native_decide` or `axiom` declarations.
4. The `zk` package pins the same toolchain and Mathlib revision as the core package, whose
   `.lake/packages` it shares.

Exits non-zero, with a message per violation, if any rule is broken.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»]+)", re.M)
LAYER1_DIRS = ["Hash", "HashTests"]
LAYER1_ALLOWED = ("Init", "Std", "Lean", "Mathlib", "Batteries", "Aesop", "Qq", "Plausible",
                  "ProofWidgets", "ImportGraph", "LeanSearchClient", "Hash", "HashTests")
LAYER1_FORBIDDEN_LOCAL = ("HashZK", "HashFFI", "HashKAT")
MATHLIB_FAMILY = ("Mathlib", "Batteries", "Aesop", "Qq", "Plausible", "ProofWidgets", "ImportGraph",
                  "LeanSearchClient")
FORBIDDEN_TOKENS = re.compile(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", re.M)


def strip_comments(src: str) -> str:
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    return re.sub(r"--[^\n]*", "", src)


# Source roots of the two packages: the core package (the repository root) and the `zk` package.
SOURCE_ROOTS = [ROOT, ROOT / "zk"]
# Package sources whose modules the HashFFI closure may reach (CompPoly's zero-import runtime
# definitions), searched after the repository. The `zk` package keeps its dependencies in the core
# package's `.lake/packages`.
PACKAGE_ROOTS = [ROOT / ".lake" / "packages" / "CompPoly"]


def module_file(mod: str) -> pathlib.Path | None:
    for base in [*SOURCE_ROOTS, *PACKAGE_ROOTS]:
        path = base / (mod.replace(".", "/") + ".lean")
        if path.exists():
            return path
    return None


def rel(path: pathlib.Path) -> pathlib.Path:
    return path.relative_to(ROOT)


def imports(path: pathlib.Path) -> list[str]:
    return IMPORT.findall(strip_comments(path.read_text()))


def top(mod: str) -> str:
    return mod.split(".")[0]


def main() -> int:
    errors: list[str] = []
    # The zk package shares the core package's `.lake/packages`, so the pins must agree.
    if (ROOT / "zk" / "lean-toolchain").read_text() != (ROOT / "lean-toolchain").read_text():
        errors.append("zk/lean-toolchain differs from lean-toolchain")
    mathlib_rev = re.compile(r'name = "mathlib"\n(?:[^\[\n]*\n)*?rev = "([^"]*)"')
    core_rev = mathlib_rev.search((ROOT / "lakefile.toml").read_text())
    zk_rev = mathlib_rev.search((ROOT / "zk" / "lakefile.toml").read_text())
    if not core_rev or not zk_rev or core_rev.group(1) != zk_rev.group(1):
        errors.append("zk/lakefile.toml must pin the same Mathlib revision as lakefile.toml")
    missing = [p for p in PACKAGE_ROOTS if not p.is_dir()]
    if missing:
        print(f"{missing[0]} not found: build the zk package first (`cd zk && lake build`)",
              file=sys.stderr)
        return 1
    layer1 = [p for d in LAYER1_DIRS for p in (ROOT / d).rglob("*.lean")] + [ROOT / "Hash.lean"]

    for path in layer1:
        rp = rel(path)
        for mod in imports(path):
            if top(mod) in LAYER1_FORBIDDEN_LOCAL or not top(mod) in LAYER1_ALLOWED:
                errors.append(f"{rp}: Layer 1 must not import {mod}")
        for m in FORBIDDEN_TOKENS.finditer(strip_comments(path.read_text())):
            errors.append(f"{rp}: forbidden in Layer 1: {m.group(0).strip()}")

    # Transitive closure of HashFFI inside the repository.
    seen: set[str] = set()
    stack = ["HashFFI"]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        path = module_file(mod)
        if path is None:
            continue
        for dep in imports(path):
            if top(dep) in MATHLIB_FAMILY or dep == "Hash.Init":
                errors.append(f"{rel(path)}: imported by HashFFI, must be Mathlib-free, imports {dep}")
            elif module_file(dep) is not None:
                stack.append(dep)

    for e in errors:
        print(e, file=sys.stderr)
    if not errors:
        print(f"layer checks passed ({len(layer1)} Layer 1 files, {len(seen)} modules in the HashFFI closure)")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
