/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
import VersoManual

/-!
# Bibliography entries for the book

Verso's citation types cover papers, articles, theses and arXiv preprints. Standards (FIPS
publications, RFCs, EIPs) have no dedicated type, so the book cites them by name, section and
link in the text; `references.bib` at the repository root lists every source.
-/

open Verso.Genre.Manual

namespace HashDocs.Bib

/-- Almeida et al., ACM CCS 2019: machine-checked indifferentiability of the SHA-3 sponge. -/
def almeida2019 : InProceedings where
  title := inlines!"Machine-Checked Proofs for Cryptographic Standards: Indifferentiability of Sponge and Secure High-Assurance Implementations of SHA-3"
  authors := #[inlines!"José Bacelar Almeida", inlines!"Cécile Baritel-Ruet",
    inlines!"Manuel Barbosa", inlines!"Gilles Barthe", inlines!"François Dupressoir",
    inlines!"Benjamin Grégoire", inlines!"Vincent Laporte", inlines!"Tiago Oliveira",
    inlines!"Alley Stoughton", inlines!"Pierre-Yves Strub"]
  year := 2019
  booktitle := inlines!"ACM SIGSAC Conference on Computer and Communications Security (CCS)"
  url := some "https://eprint.iacr.org/2019/1155"

/-- Appel, ACM TOPLAS 2015: verification of OpenSSL's SHA-256 against FIPS 180-4 in Coq. -/
def appel2015 : Article where
  title := inlines!"Verification of a Cryptographic Primitive: SHA-256"
  authors := #[inlines!"Andrew W. Appel"]
  journal := inlines!"ACM Transactions on Programming Languages and Systems"
  year := 2015
  month := none
  volume := inlines!"37"
  number := inlines!"2"
  url := some "https://www.cs.princeton.edu/~appel/papers/verif-sha-2.pdf"

end HashDocs.Bib
