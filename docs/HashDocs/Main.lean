/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import VersoManual
import HashDocs

open Verso.Genre.Manual

/-- Build the book. Run from the repository root: `lake exe hash-docs --output _site`. -/
def main := manualMain (%doc HashDocs) (config := {
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1
  extraFiles := [("docs/static", "static")]
})
