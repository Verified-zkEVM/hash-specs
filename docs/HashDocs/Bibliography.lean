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

/-- Merkle, CRYPTO 1989: one of the two original iterated hash constructions. -/
def merkle1989 : InProceedings where
  title := inlines!"One Way Hash Functions and DES"
  authors := #[inlines!"Ralph C. Merkle"]
  year := 1989
  booktitle := inlines!"Advances in Cryptology – CRYPTO '89, LNCS 435"
  url := some "https://doi.org/10.1007/0-387-34805-0_40"

/-- Damgård, CRYPTO 1989: collision resistance of the iterated construction. -/
def damgard1989 : InProceedings where
  title := inlines!"A Design Principle for Hash Functions"
  authors := #[inlines!"Ivan Bjerre Damgård"]
  year := 1989
  booktitle := inlines!"Advances in Cryptology – CRYPTO '89, LNCS 435"
  url := some "https://doi.org/10.1007/0-387-34805-0_39"

/-- Coron, Dodis, Malinaud and Puniya, CRYPTO 2005: Merkle–Damgård is not indifferentiable
from a random oracle. -/
def coron2005 : InProceedings where
  title := inlines!"Merkle-Damgård Revisited: How to Construct a Hash Function"
  authors := #[inlines!"Jean-Sébastien Coron", inlines!"Yevgeniy Dodis",
    inlines!"Cécile Malinaud", inlines!"Prashant Puniya"]
  year := 2005
  booktitle := inlines!"Advances in Cryptology – CRYPTO 2005, LNCS 3621"
  url := some "https://doi.org/10.1007/11535218_26"

/-- Mendel, Nad and Schläffer, EUROCRYPT 2013: collisions for step-reduced SHA-256. -/
def mendel2013 : InProceedings where
  title := inlines!"Improving Local Collisions: New Attacks on Reduced SHA-256"
  authors := #[inlines!"Florian Mendel", inlines!"Tomislav Nad", inlines!"Martin Schläffer"]
  year := 2013
  booktitle := inlines!"Advances in Cryptology – EUROCRYPT 2013, LNCS 7881"
  url := some "https://doi.org/10.1007/978-3-642-38348-9_16"

/-- Li, Liu and Wang, EUROCRYPT 2024: new records in collision attacks on SHA-2. -/
def li2024 : InProceedings where
  title := inlines!"New Records in Collision Attacks on SHA-2"
  authors := #[inlines!"Yingxin Li", inlines!"Fukang Liu", inlines!"Gaoli Wang"]
  year := 2024
  booktitle := inlines!"Advances in Cryptology – EUROCRYPT 2024"
  url := some "https://eprint.iacr.org/2024/349"

/-- Khovratovich, Rechberger and Savelieva, FSE 2012: biclique preimage attacks on reduced
SHA-2. -/
def khovratovich2012 : InProceedings where
  title := inlines!"Bicliques for Preimages: Attacks on Skein-512 and the SHA-2 Family"
  authors := #[inlines!"Dmitry Khovratovich", inlines!"Christian Rechberger",
    inlines!"Alexandra Savelieva"]
  year := 2012
  booktitle := inlines!"Fast Software Encryption (FSE 2012)"
  url := some "https://eprint.iacr.org/2011/286"

/-- Bertoni, Daemen, Peeters and Van Assche, EUROCRYPT 2008: the sponge construction is
indifferentiable from a random oracle. -/
def bertoni2008 : InProceedings where
  title := inlines!"On the Indifferentiability of the Sponge Construction"
  authors := #[inlines!"Guido Bertoni", inlines!"Joan Daemen", inlines!"Michaël Peeters",
    inlines!"Gilles Van Assche"]
  year := 2008
  booktitle := inlines!"Advances in Cryptology – EUROCRYPT 2008, LNCS 4965"
  url := some "https://doi.org/10.1007/978-3-540-78967-3_11"

/-- Aumasson, Neves, Wilcox-O'Hearn and Winnerlein, ACNS 2013: the BLAKE2 design. -/
def aumasson2013 : InProceedings where
  title := inlines!"BLAKE2: Simpler, Smaller, Fast as MD5"
  authors := #[inlines!"Jean-Philippe Aumasson", inlines!"Samuel Neves",
    inlines!"Zooko Wilcox-O'Hearn", inlines!"Christian Winnerlein"]
  year := 2013
  booktitle := inlines!"Applied Cryptography and Network Security (ACNS 2013), LNCS 7954"
  url := some "https://doi.org/10.1007/978-3-642-38980-1_8"

/-- Guo, Karpman, Nikolić, Wang and Wu, CT-RSA 2014: cryptanalysis of BLAKE2. -/
def guo2014 : InProceedings where
  title := inlines!"Analysis of BLAKE2"
  authors := #[inlines!"Jian Guo", inlines!"Pierre Karpman", inlines!"Ivica Nikolić",
    inlines!"Lei Wang", inlines!"Shuang Wu"]
  year := 2014
  booktitle := inlines!"Topics in Cryptology – CT-RSA 2014"
  url := some "https://eprint.iacr.org/2013/467"

/-- Luykx, Mennink and Neves, ToSC 2016: security of BLAKE2's modes of operation. -/
def luykx2016 : Article where
  title := inlines!"Security Analysis of BLAKE2's Modes of Operation"
  authors := #[inlines!"Atul Luykx", inlines!"Bart Mennink", inlines!"Samuel Neves"]
  journal := inlines!"IACR Transactions on Symmetric Cryptology"
  year := 2016
  month := none
  volume := inlines!"2016"
  number := inlines!"1"
  url := some "https://doi.org/10.13154/tosc.v2016.i1.158-176"

/-- Grassi, Khovratovich, Rechberger, Roy and Schofnegger, USENIX Security 2021: the Poseidon
permutation and hash. -/
def grassi2021 : InProceedings where
  title := inlines!"Poseidon: A New Hash Function for Zero-Knowledge Proof Systems"
  authors := #[inlines!"Lorenzo Grassi", inlines!"Dmitry Khovratovich",
    inlines!"Christian Rechberger", inlines!"Arnab Roy", inlines!"Markus Schofnegger"]
  year := 2021
  booktitle := inlines!"30th USENIX Security Symposium"
  url := some "https://eprint.iacr.org/2019/458"

/-- Bariant, Bouvier, Leurent and Perrin, ToSC 2022: algebraic attacks on round-reduced
Poseidon and other arithmetization-oriented primitives. -/
def bariant2022 : Article where
  title := inlines!"Algebraic Attacks against Some Arithmetization-Oriented Primitives"
  authors := #[inlines!"Augustin Bariant", inlines!"Clémence Bouvier", inlines!"Gaëtan Leurent",
    inlines!"Léo Perrin"]
  journal := inlines!"IACR Transactions on Symmetric Cryptology"
  year := 2022
  month := none
  volume := inlines!"2022"
  number := inlines!"3"
  url := some "https://doi.org/10.46586/tosc.v2022.i3.73-101"

end HashDocs.Bib
