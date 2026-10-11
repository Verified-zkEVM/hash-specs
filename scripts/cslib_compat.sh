#!/usr/bin/env bash
# Build Layer 1 (Hash, HashTests) against CSLib's current Lean toolchain and Mathlib commit.
# Advisory only (ROADMAP.md §6.2): a failure here is tracked but does not block anything.
#
# Usage: scripts/cslib_compat.sh [work-dir]
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
work=${1:-$(mktemp -d)}
base=https://raw.githubusercontent.com/leanprover/cslib/main

toolchain=$(curl -fsSL "$base/lean-toolchain")
mathlib_rev=$(curl -fsSL "$base/lake-manifest.json" | python3 -c \
  'import json, sys; print(next(p["rev"] for p in json.load(sys.stdin)["packages"] if p["name"] == "mathlib"))')
echo "CSLib toolchain: $toolchain; Mathlib: $mathlib_rev"

rm -rf "$work" && mkdir -p "$work"
cp -R "$root/Hash" "$root/Hash.lean" "$root/HashTests" "$root/HashTests.lean" "$work/"
echo "$toolchain" > "$work/lean-toolchain"
python3 - "$root/lakefile.toml" "$work/lakefile.toml" "$mathlib_rev" <<'PY'
import re, sys
src, dst, rev = sys.argv[1:]
text = open(src).read()
options = re.search(r"\[leanOptions\].*?(?=\n\[\[)", text, re.S).group(0)
open(dst, "w").write(f'''name = "hash-specs-cslib-compat"
defaultTargets = ["Hash", "HashTests"]

{options}

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "{rev}"

[[lean_lib]]
name = "Hash"

[[lean_lib]]
name = "HashTests"
globs = ["HashTests.+"]
''')
PY
cd "$work"
lake update
lake exe cache get
lake build Hash HashTests
