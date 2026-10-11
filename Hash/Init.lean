/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module -- shake: keep-downstream, shake: keep-all

public import Mathlib.Init
public import Mathlib.Tactic.Common

/-!
# Initialization for Mathlib-based files

This file mirrors `Cslib.Init` (see `ROADMAP.md` §2.1 and §6.2): it is imported by every
Layer 1 file that uses Mathlib, and it activates Mathlib's default linters and common tactics.
If the core is upstreamed to CSLib, imports of this file become imports of `Cslib.Init`.

Files that do not need Mathlib (bit and byte utilities, the reference and fast specifications of
the byte-oriented hashes) do not import it, so that a Mathlib-free part of the library can be
split off later.
-/
