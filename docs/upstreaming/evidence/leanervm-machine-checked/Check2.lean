import Hash.BLAKE2.API

/-! Transcriptions (verbatim modulo namespaces) of
  leanerVM a37b2b0: LeanerVM/Parameters/Blake2s.lean, Semantics/Blake2s.lean:64-110,
    Protocol/Blake2sHash.lean:52-94
  machine-checked 5b1f8a5: Cases/Zip2005/Spec/Zip2005/Blake2b.lean:53-210, Encoding.lean:72 -/

namespace LVM
def iv : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
def sigma : Vector (Vector (Fin 16) 16) 10 := #v[
  #v[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #v[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #v[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #v[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #v[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #v[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #v[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #v[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #v[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #v[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]
def rotr (x : UInt32) (n : Nat) : UInt32 := ⟨x.toBitVec.rotateRight n⟩
def mix (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32) : Vector UInt32 16 :=
  let va := v[a] + v[b] + x
  let vd := rotr (v[d] ^^^ va) 16
  let vc := v[c] + vd
  let vb := rotr (v[b] ^^^ vc) 12
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((v.set a va).set b vb).set c vc).set d vd
def round (v m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Vector UInt32 16 :=
  let v := mix v 0 4 8 12 m[s[0]] m[s[1]]
  let v := mix v 1 5 9 13 m[s[2]] m[s[3]]
  let v := mix v 2 6 10 14 m[s[4]] m[s[5]]
  let v := mix v 3 7 11 15 m[s[6]] m[s[7]]
  let v := mix v 0 5 10 15 m[s[8]] m[s[9]]
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mix v 2 7 8 13 m[s[12]] m[s[13]]
  mix v 3 4 9 14 m[s[14]] m[s[15]]
def initialState (h : Vector UInt32 8) (t : UInt64) (f0 f1 : UInt32) : Vector UInt32 16 :=
  let v : Vector UInt32 16 := h ++ iv
  let v := v.set 12 (v[12] ^^^ t.toUInt32)
  let v := v.set 13 (v[13] ^^^ (t >>> 32).toUInt32)
  let v := v.set 14 (v[14] ^^^ f0)
  v.set 15 (v[15] ^^^ f1)
def compress (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ round v m s) (initialState h t f0 f1)
  #v[h[0] ^^^ v[0] ^^^ v[8], h[1] ^^^ v[1] ^^^ v[9], h[2] ^^^ v[2] ^^^ v[10],
     h[3] ^^^ v[3] ^^^ v[11], h[4] ^^^ v[4] ^^^ v[12], h[5] ^^^ v[5] ^^^ v[13],
     h[6] ^^^ v[6] ^^^ v[14], h[7] ^^^ v[7] ^^^ v[15]]
def lastBlock : UInt32 := 0xFFFFFFFF
def paramIv : Vector UInt32 8 := iv.set 0 (iv[0] ^^^ 0x01010020)
def leWord (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
def blockWords (block : List UInt8) : Vector UInt32 16 :=
  let b := fun i ↦ block.getD i 0
  Vector.ofFn fun j ↦ leWord (b (4 * j)) (b (4 * j + 1)) (b (4 * j + 2)) (b (4 * j + 3))
def absorb (h : Vector UInt32 8) (t : Nat) : (blocks : Nat) → List UInt8 → Vector UInt32 8
  | 0, data => compress h (blockWords data) (t + data.length).toUInt64 lastBlock 0
  | blocks + 1, data =>
    absorb (compress h (blockWords (data.take 64)) (t + 64).toUInt64 0 0) (t + 64) blocks
      (data.drop 64)
def blake2sBytes (data : List UInt8) : Vector UInt32 8 :=
  absorb paramIv 0 ((data.length - 1) / 64) data
def wordBytes (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]
def digestBytes (d : Vector UInt32 8) : List UInt8 := d.toList.flatMap wordBytes
end LVM

namespace Zip
def leos2ip (S : List UInt8) : Nat := S.foldr (fun b acc => b.toNat + 256 * acc) 0
def M64 : Nat := 2 ^ 64
def IV : List Nat :=
  [0x6A09E667F3BCC908, 0xBB67AE8584CAA73B, 0x3C6EF372FE94F82B,
   0xA54FF53A5F1D36F1, 0x510E527FADE682D1, 0x9B05688C2B3E6C1F,
   0x1F83D9ABFB41BD6B, 0x5BE0CD19137E2179]
def sigma : List (List Nat) :=
  [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
   [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
   [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
   [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
   [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
   [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
   [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
   [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
   [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
   [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]]
def mixTable : List (Nat × Nat × Nat × Nat) :=
  [(0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15),
   (0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14)]
def rounds : Nat := 12
def blockBytes : Nat := 128
def rotr (n : Nat) (x : Nat) : Nat := ((x >>> n) ||| (x <<< (64 - n))) % M64
def G (v : List Nat) (a b c d : Nat) (x y : Nat) : List Nat := Id.run do
  let mut v := v
  v := v.set a ((v.getD a 0 + v.getD b 0 + x) % M64)
  v := v.set d (rotr 32 (v.getD d 0 ^^^ v.getD a 0))
  v := v.set c ((v.getD c 0 + v.getD d 0) % M64)
  v := v.set b (rotr 24 (v.getD b 0 ^^^ v.getD c 0))
  v := v.set a ((v.getD a 0 + v.getD b 0 + y) % M64)
  v := v.set d (rotr 16 (v.getD d 0 ^^^ v.getD a 0))
  v := v.set c ((v.getD c 0 + v.getD d 0) % M64)
  v := v.set b (rotr 63 (v.getD b 0 ^^^ v.getD c 0))
  pure v
def mixRounds (h m : List Nat) (t0 t1 : Nat) (f : Bool) : List Nat := Id.run do
  let mut v := h ++ IV
  v := v.set 12 ((v.getD 12 0) ^^^ t0)
  v := v.set 13 ((v.getD 13 0) ^^^ t1)
  if f then
    v := v.set 14 ((v.getD 14 0) ^^^ (M64 - 1))
  for rnd in [0:rounds] do
    let sch := sigma.getD (rnd % 10) []
    let mut i := 0
    for (a, b, c, d) in mixTable do
      v := G v a b c d (m.getD (sch.getD (2*i) 0) 0) (m.getD (sch.getD (2*i+1) 0) 0)
      i := i + 1
  pure v
def compress (h m : List Nat) (t0 t1 : Nat) (f : Bool) : List Nat :=
  let v := mixRounds h m t0 t1 f
  (List.range 8).map (fun i => (h.getD i 0) ^^^ (v.getD i 0) ^^^ (v.getD (i+8) 0))
def leWords (data : List UInt8) (start count : Nat) : List Nat :=
  (List.range count).map (fun i => leos2ip ((data.drop (start + 8*i)).take 8))
def wordBytes (w : Nat) : List UInt8 :=
  (List.range 8).map (fun i => UInt8.ofNat (w >>> (8*i) % 256))
def stateBytes (h : List Nat) : List UInt8 := h.flatMap wordBytes
def paramWord0 (digestLen keyLen : Nat) : Nat :=
  digestLen ||| (keyLen <<< 8) ||| (1 <<< 16) ||| (1 <<< 24)
def initialState (digestLen keyLen : Nat) (salt personal : List UInt8) : List Nat :=
  Id.run do
    let mut h := IV
    h := h.set 0 ((h.getD 0 0) ^^^ paramWord0 digestLen keyLen)
    h := h.set 4 ((h.getD 4 0) ^^^ leos2ip (salt.take 8))
    h := h.set 5 ((h.getD 5 0) ^^^ leos2ip ((salt.drop 8).take 8))
    h := h.set 6 ((h.getD 6 0) ^^^ leos2ip (personal.take 8))
    h := h.set 7 ((h.getD 7 0) ^^^ leos2ip ((personal.drop 8).take 8))
    pure h
def blockCount (ll : Nat) : Nat := max 1 ((ll + blockBytes - 1) / blockBytes)
def absorbAux (msg : List UInt8) (h : List Nat) (i k : Nat) : List Nat :=
  match k with
  | 0 => h
  | k + 1 =>
      let h' := compress h (leWords msg (i * blockBytes) 16) ((i + 1) * blockBytes) 0 false
      absorbAux msg h' (i + 1) k
def blake2b (personal : List UInt8) (nn : Nat) (msg : List UInt8) : List UInt8 :=
  let ll := msg.length
  let dd := blockCount ll
  let h0 := initialState nn 0 [] personal
  let h1 := absorbAux msg h0 0 (dd - 1)
  let hFinal := compress h1 (leWords msg ((dd - 1) * blockBytes) 16) ll 0 true
  (stateBytes hFinal).take nn
def pers : List UInt8 := "Zcash_ExpandSeed".toList.map (fun c => UInt8.ofNat c.toNat)
end Zip

namespace B2b
abbrev Word := BitVec 64
def rotr (n : Nat) (x : Word) : Word := x >>> n ||| x <<< (64 - n)
def Gw (a b c d x y : Word) : Word × Word × Word × Word :=
  let a := a + b + x
  let d := rotr 32 (d ^^^ a)
  let c := c + d
  let b := rotr 24 (b ^^^ c)
  let a := a + y + b
  let d := rotr 16 (d ^^^ a)
  let c := c + d
  let b := rotr 63 (b ^^^ c)
  (a, b, c, d)
def G (v : List Word) (a b c d : Nat) (x y : Word) : List Word :=
  let r := Gw (v.getD a 0) (v.getD b 0) (v.getD c 0) (v.getD d 0) x y
  (((v.set a r.1).set b r.2.1).set c r.2.2.1).set d r.2.2.2
def IV : List Word := Hash.BLAKE2.blake2bParams.IV.map (BitVec.ofNat 64)
def roundWith (v m : List Word) (s : List Nat) : List Word :=
  let mw := fun i => m.getD (s.getD i 0) 0
  let v := G v 0 4 8 12 (mw 0) (mw 1)
  let v := G v 1 5 9 13 (mw 2) (mw 3)
  let v := G v 2 6 10 14 (mw 4) (mw 5)
  let v := G v 3 7 11 15 (mw 6) (mw 7)
  let v := G v 0 5 10 15 (mw 8) (mw 9)
  let v := G v 1 6 11 12 (mw 10) (mw 11)
  let v := G v 2 7 8 13 (mw 12) (mw 13)
  G v 3 4 9 14 (mw 14) (mw 15)
def round (v m : List Word) (r : Nat) : List Word := roundWith v m (Zip.sigma.getD (r % 10) [])
def initV (h : List Word) (t0 t1 fb fn : Word) : List Word :=
  let v := h ++ IV
  let v := v.set 12 (v.getD 12 0 ^^^ t0)
  let v := v.set 13 (v.getD 13 0 ^^^ t1)
  let v := v.set 14 (v.getD 14 0 ^^^ fb)
  v.set 15 (v.getD 15 0 ^^^ fn)
def roundsTo (h m : List Word) (t0 t1 fb fn : Word) (k : Nat) : List Word :=
  (List.range k).foldl (fun v r => round v m r) (initV h t0 t1 fb fn)
def compress (h m : List Word) (t0 t1 fb fn : Word) : List Word :=
  let v := roundsTo h m t0 t1 fb fn 12
  (List.range 8).map (fun i => h.getD i 0 ^^^ v.getD i 0 ^^^ v.getD (i + 8) 0)
end B2b

def prng (seed n : Nat) : List UInt8 :=
  ((List.range n).foldl (fun (s, acc) _ =>
    let s := (s * 6364136223846793005 + 1442695040888963407) % 2^64
    (s, (s / 2^56).toUInt8 :: acc)) (seed, [])).2.reverse
def words64 (seed n : Nat) : List Nat :=
  (List.range n).map fun i => Zip.leos2ip (prng (seed * 37 + i) 8)

-- machine-checked B2b model (BitVec 64) vs Hash.BLAKE2.Reference.F blake2bParams 12
#eval (List.range 100).all fun s =>
  let h := (words64 s 8).map (BitVec.ofNat 64)
  let m := (words64 (s + 1000) 16).map (BitVec.ofNat 64)
  let t0 := Zip.leos2ip (prng (s + 5000) 8)
  let t1 := Zip.leos2ip (prng (s + 6000) 8)
  let f := s % 2 == 0
  B2b.compress h m (BitVec.ofNat 64 t0) (BitVec.ofNat 64 t1) (if f then 0xFFFFFFFFFFFFFFFF#64 else 0#64) 0#64 ==
    Hash.BLAKE2.Reference.F Hash.BLAKE2.blake2bParams 12 h m (t0 + 2^64 * t1) f

-- leanerVM compress (Vector UInt32) vs Reference.F blake2sParams 10 over BitVec 32
#eval (List.range 100).all fun s =>
  let h := (List.range 8).map fun i => (Zip.leos2ip (prng (s*8+i) 4)).toUInt32
  let m := (List.range 16).map fun i => (Zip.leos2ip (prng (s*16+i+999) 4)).toUInt32
  let t : UInt64 := (Zip.leos2ip (prng (s + 5000) 8)).toUInt64
  let f := s % 2 == 0
  let hv : Vector UInt32 8 := ⟨h.toArray, by simp [h]⟩
  let mv : Vector UInt32 16 := ⟨m.toArray, by simp [m]⟩
  (LVM.compress hv mv t (if f then 0xFFFFFFFF else 0) 0).toList.map UInt32.toBitVec ==
    Hash.BLAKE2.Reference.F Hash.BLAKE2.blake2sParams 10 (h.map UInt32.toBitVec) (m.map UInt32.toBitVec) t.toNat f

-- last-node flag: leanerVM's hashlib vector (empty msg, last_node) is not reachable via F's Bool flag
#eval (LVM.compress LVM.paramIv ⟨(List.replicate 16 (0:UInt32)).toArray, by simp⟩ 0 0xFFFFFFFF 0xFFFFFFFF).toList
  == [0x3c11fc24, 0x848cbe3d, 0x40703c49, 0x680dafae, 0xab7b3bcc, 0x49aecd0d, 0x704abbdb, 0x365c9d25]
