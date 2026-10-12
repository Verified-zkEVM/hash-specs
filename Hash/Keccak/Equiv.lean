/-
Copyright (c) 2026 Derek Sorensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Hash.Keccak.API
public import Hash.Keccak.Properties

/-!
# Keccak: the fast specification equals the reference

The lane-based Keccak-f[1600] of `Hash.Keccak.Fast` computes the reference Keccak-p[1600, 24] of
`Hash.Keccak.KeccakP` (`Hash.Keccak.Equiv.keccakP_toString`), and the byte-level sponge computes
the reference KECCAK[c] on byte-aligned messages. Consequently each function of
`Hash.Keccak.API` equals its reference, for example `Hash.Keccak.sha3x256_eq`.

The correspondence between the two state representations is `toState`: bit `z` of lane
`x + 5y` is the state bit `A[x, y, z]`.
-/

public section

namespace Hash.Keccak.Equiv

open Fast

/-- The state array denoted by 25 lanes: `A[x, y, z]` is bit `z` of lane `x + 5y`. -/
def toState (a : Array UInt64) : State 64 :=
  fun x y z => (lane a (x.val + 5 * y.val)).toBitVec.getLsbD z.val

theorem lane_tabulate (n : Nat) (f : Nat → UInt64) (i : Nat) (h : i < n) :
    lane (tabulate n f) i = f i := by
  simp [lane, tabulate, h]

theorem val_three : ((3 : Fin 5) : Nat) = 3 := rfl
theorem val_four : ((4 : Fin 5) : Nat) = 4 := rfl

/-! ### The step mappings -/

theorem toState_theta (a : Array UInt64) : toState (theta a) = θ (toState a) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have hxm1 : (x - 1).val = (x.val + 4) % 5 := by rw [Fin.sub_def]; simp; omega
  have hxp1 : (x + 1).val = (x.val + 1) % 5 := by simp [Fin.val_add]
  have hzs : (zsub z 1).val = (z.val + 63) % 64 := by simp [zsub]
  simp only [toState, theta, θ, D, C, lane_tabulate _ _ _ (show x.val + 5 * y.val < 25 by omega),
    show (x.val + 5 * y.val) % 5 = x.val by omega, lane_tabulate _ _ _ hx,
    lane_tabulate _ _ _ (show (x.val + 4) % 5 < 5 by omega),
    lane_tabulate _ _ _ (show (x.val + 1) % 5 < 5 by omega),
    UInt64.toBitVec_xor, BitVec.getLsbD_xor, hxm1, hxp1, hzs,
    show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, UInt64.toBitVec_rotl _ 1 (by decide),
    BitVec.getLsbD_rotateLeft, Fin.val_zero, Fin.val_one, Fin.val_two, val_three, val_four,
    Nat.one_mod, Fin.isValue]
  rcases Nat.eq_zero_or_pos z.val with h0 | h0
  · simp [h0]
  · have : (z.val + 63) % 64 = z.val - 1 := by omega
    simp [this, show ¬ z.val < 1 by omega, hz]

/-- The ρ rotation table agrees with the ρ offsets of the reference. -/
theorem rhoRotations_getD (x y : Fin 5) :
    rhoRotations.getD (x.val + 5 * y.val) 0 = (ρOffset x y % 64).toUInt64 := by
  revert x y
  decide +kernel

theorem toState_rho (a : Array UInt64) : toState (rho a) = ρ (toState a) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have hn : ρOffset x y % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [toState, rho, ρ, lane_tabulate _ _ _ (show x.val + 5 * y.val < 25 by omega),
    rhoRotations_getD, UInt64.toBitVec_rotl _ _ hn, BitVec.getLsbD_rotateLeft, zsub]
  generalize ρOffset x y = n at hn ⊢
  rw [Nat.mod_mod]
  by_cases h : z.val < n % 64
  · simp [h, show (z.val + (64 - n % 64)) % 64 = 64 - n % 64 + z.val by omega]
  · simp [h, hz, show (z.val + (64 - n % 64)) % 64 = z.val - n % 64 by omega]

theorem toState_pi (a : Array UInt64) : toState (pi a) = π (toState a) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hxy : (x + 3 * y).val = (x.val + 3 * y.val) % 5 := by
    simp only [Fin.val_add, Fin.val_mul]
    rw [show ((3 : Fin 5) : Nat) = 3 from rfl]
    omega
  simp only [toState, pi, π, lane_tabulate _ _ _ (show x.val + 5 * y.val < 25 by omega),
    show (x.val + 5 * y.val) % 5 = x.val by omega, show (x.val + 5 * y.val) / 5 = y.val by omega,
    hxy]

theorem toState_chi (a : Array UInt64) : toState (chi a) = χ (toState a) := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have hxp1 : (x + 1).val = (x.val + 1) % 5 := by simp [Fin.val_add]
  have hxp2 : (x + 2).val = (x.val + 2) % 5 := by simp [Fin.val_add]
  simp only [toState, chi, χ, lane_tabulate _ _ _ (show x.val + 5 * y.val < 25 by omega),
    show (x.val + 5 * y.val) % 5 = x.val by omega, show (x.val + 5 * y.val) / 5 = y.val by omega,
    hxp1, hxp2, UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hz, decide_true,
    Bool.true_and, Bool.xor_true]

/-- The round-constant words agree with the round constants of the reference. -/
theorem roundConstantWords_getLsbD (ir : Fin 24) (z : Fin 64) :
    (roundConstantWords.getD ir.val 0).toBitVec.getLsbD z.val = RC 6 ir.val z.val := by
  revert ir z
  decide +kernel

theorem toState_iota (a : Array UInt64) (ir : Nat) (hir : ir < 24) :
    toState (iota a ir) = ι 6 (toState a) ir := by
  funext x y z
  have hx := x.isLt
  have hy := y.isLt
  simp only [toState, iota, ι, lane_tabulate _ _ _ (show x.val + 5 * y.val < 25 by omega)]
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, and_self, ↓reduceIte,
      UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    rw [roundConstantWords_getLsbD ⟨ir, hir⟩ z]
  · have : x.val + 5 * y.val ≠ 0 := by
      intro h0
      exact h ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
    simp [h]

theorem toState_round (a : Array UInt64) (ir : Nat) (hir : ir < 24) :
    toState (round a ir) = Rnd 6 (toState a) ir := by
  rw [round, toState_iota _ _ hir, toState_chi, toState_pi, toState_rho, toState_theta]
  rfl

theorem toState_keccakF (a : Array UInt64) :
    toState (Fast.keccakF a) =
      (List.range 24).foldl (fun A (i : Nat) => Rnd 6 A ((12 + 2 * 6 : Nat) - 24 + i : Int))
        (toState a) := by
  unfold Fast.keccakF
  rw [foldl_hom_of_mem toState round _ (List.range 24) a]
  intro b i hi
  rw [toState_round _ _ (List.mem_range.1 hi)]
  congr 1
  omega

/-- Keccak-f[1600] on lanes computes Keccak-p[1600, 24] on strings. -/
theorem keccakP_toString (a : Array UInt64) :
    keccakP 6 24 (toState a).toString = (toState (Fast.keccakF a)).toString := by
  rw [keccakP_eq_algorithm7 _ _ _ (by simp), State.ofString_toString, toState_keccakF]
  rfl

/-! ### The state as a string -/

theorem getElem?_toString_toState (a : Array UInt64) (i z : Nat) (hi : i < 25) (hz : z < 64) :
    (toState a).toString[64 * i + z]? = some ((lane a i).toBitVec.getLsbD z) := by
  have h := State.getElem?_toString (toState a) ⟨i % 5, Nat.mod_lt _ (by decide)⟩
    ⟨i / 5, by omega⟩ ⟨z, hz⟩
  simp only [toState] at h
  rw [show 64 * (5 * (i / 5) + i % 5) + z = 64 * i + z by omega,
    show i % 5 + 5 * (i / 5) = i by omega] at h
  exact h

theorem toString_toState_zeros :
    (toState (Array.replicate 25 0)).toString = List.replicate 1600 false := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 1600
  · rw [show k = 64 * (k / 64) + k % 64 by omega,
      getElem?_toString_toState _ _ _ (by omega) (by omega), List.getElem?_replicate]
    have hc : 64 * (k / 64) + k % 64 < 1600 := by omega
    have hl : lane (Array.replicate 25 0) (k / 64) = 0 := by
      simp only [lane, Array.getD_eq_getD_getElem?, Array.getElem?_replicate,
        show k / 64 < 25 by omega, ↓reduceIte, Option.getD_some]
    simp only [hc, ↓reduceIte, hl]
    simp
  · rw [List.getElem?_eq_none (by rw [State.length_toString]; omega),
      List.getElem?_eq_none (by rw [List.length_replicate]; omega)]

/-! ### Absorbing -/

/-- XORing a block of `rate` bytes into the lanes XORs its bits into the first `8 · rate` bits
of the string. -/
theorem toString_xorBlock (rate : Nat) (h8 : rate % 8 = 0) (h200 : rate ≤ 200)
    (a : Array UInt64) (p : ByteArray) (off : Nat) (hoff : off + rate ≤ p.size) :
    (toState (tabulate 25 fun i =>
        if i < rate / 8 then lane a i ^^^ ByteArray.getUInt64LE p (off + 8 * i) else lane a i)
      ).toString =
      Sponge.xorBits (toState a).toString
        (bytesToBitsLSB ((p.data.toList.drop off).take rate) ++
          List.replicate (1600 - 8 * rate) false) := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < 1600
  · have hi : k / 64 < 25 := by omega
    have hz : k % 64 < 64 := Nat.mod_lt _ (by decide)
    rw [Sponge.xorBits, List.getElem?_zipWith, show k = 64 * (k / 64) + k % 64 by omega,
      getElem?_toString_toState _ _ _ hi hz, getElem?_toString_toState _ _ _ hi hz,
      lane_tabulate _ _ _ hi]
    by_cases hb : k / 64 < rate / 8
    · have hk8 : 64 * (k / 64) + k % 64 = 8 * (8 * (k / 64) + k % 64 / 8) + k % 64 % 8 := by
        omega
      have hsz : p.data.size = p.size := rfl
      have hlen : 8 * (k / 64) + k % 64 / 8 < ((p.data.toList.drop off).take rate).length := by
        simp only [List.length_take, List.length_drop, Array.length_toList]
        omega
      rw [List.getElem?_append_left (by simp; omega), hk8,
        getElem?_bytesToBitsLSB _ _ _ hlen (by omega)]
      simp only [hb, ↓reduceIte, UInt64.toBitVec_xor, BitVec.getLsbD_xor, Option.some.injEq,
        List.getElem_take, List.getElem_drop, Array.getElem_toList]
      congr 1
      rw [BitVec.getLsbD, UInt64.toNat_toBitVec, ByteArray.testBit_getUInt64LE _ _ _ hz,
        show off + 8 * (k / 64) + k % 64 / 8 = off + (8 * (k / 64) + k % 64 / 8) by omega]
      rw [ByteArray.get!, getElem!_pos p.data (off + (8 * (k / 64) + k % 64 / 8)) (by omega)]
    · have hsz : p.data.size = p.size := rfl
      have hm : ((p.data.toList.drop off).take rate).length = rate := by
        simp only [List.length_take, List.length_drop, Array.length_toList]
        omega
      have hc : 64 * (k / 64) + k % 64 - 8 * rate < 1600 - 8 * rate := by omega
      rw [List.getElem?_append_right (by simp only [length_bytesToBitsLSB, hm]; omega),
        List.getElem?_replicate, length_bytesToBitsLSB, hm]
      simp only [hc, ↓reduceIte, hb, Bool.xor_false]
  · rw [List.getElem?_eq_none (by simp; omega)]
    rw [Sponge.xorBits, List.getElem?_zipWith, List.getElem?_eq_none (l := (toState a).toString)
      (by simp; omega)]

/-- Absorbing one block on lanes is absorbing it on strings. -/
theorem toString_absorbBlock (rate : Nat) (h8 : rate % 8 = 0) (h200 : rate ≤ 200)
    (a : Array UInt64) (p : ByteArray) (off : Nat) (hoff : off + rate ≤ p.size) :
    (toState (absorbBlock rate a p off)).toString =
      keccakP 6 24 (Sponge.xorBits (toState a).toString
        (bytesToBitsLSB ((p.data.toList.drop off).take rate) ++
          List.replicate (1600 - 8 * rate) false)) := by
  rw [absorbBlock, ← keccakP_toString, toString_xorBlock rate h8 h200 a p off hoff]

/-! ### Squeezing -/

/-- The bytes of the first `n` lanes are the first `64 n` bits of the string. -/
theorem bytesToBitsLSB_lanes (a : Array UInt64) (n : Nat) (hn : n ≤ 25) :
    bytesToBitsLSB ((List.range n).foldl (fun out i => ByteArray.pushUInt64LE out (lane a i))
      ByteArray.empty).data.toList = (toState a).toString.take (64 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      ByteArray.bytesToBitsLSB_pushUInt64LE, ih (by omega), show 64 * (n + 1) = 64 * n + 64 by ring,
      List.take_add]
    congr 1
    apply List.ext_getElem?
    intro z
    by_cases hz : z < 64
    · rw [getElem?_natToBitsLE _ _ _ hz, List.getElem?_take_of_lt hz, List.getElem?_drop,
        getElem?_toString_toState _ _ _ (by omega) hz, BitVec.getLsbD, UInt64.toNat_toBitVec]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

theorem bytesToBitsLSB_rateBytes (rate : Nat) (h8 : rate % 8 = 0) (h200 : rate ≤ 200)
    (a : Array UInt64) :
    bytesToBitsLSB (rateBytes rate a).data.toList = (toState a).toString.take (8 * rate) := by
  rw [rateBytes, bytesToBitsLSB_lanes _ _ (by omega), show 64 * (rate / 8) = 8 * rate by omega]

theorem bytesToBitsLSB_squeeze (rate : Nat) (h8 : rate % 8 = 0) (h200 : rate ≤ 200)
    (a : Array UInt64) (k : Nat) (out : ByteArray) :
    bytesToBitsLSB (squeeze rate a k out).data.toList =
      bytesToBitsLSB out.data.toList ++
        Sponge.squeeze (keccakP 6 24) (8 * rate) (toState a).toString k := by
  induction k generalizing a out with
  | zero => simp [squeeze, Sponge.squeeze]
  | succ k ih =>
    rw [squeeze, ih, Sponge.squeeze, ByteArray.data_append, Array.toList_append,
      bytesToBitsLSB_append, bytesToBitsLSB_rateBytes rate h8 h200, keccakP_toString,
      List.append_assoc]

/-! ### Padding -/

/-- The rates, in bytes, of the members of FIPS 202 and of Keccak-256. -/
def Rate (rate : Nat) : Prop :=
  rate = 72 ∨ rate = 104 ∨ rate = 136 ∨ rate = 144 ∨ rate = 168

/-- A domain-separation byte for the suffix bits `suffix`: its bits are the suffix, then the
first bit of pad10*1, then zeros; with the top bit set, the last bit of pad10*1 too. -/
structure DomainByte (ds : UInt8) (suffix : List Bool) : Prop where
  length_le : suffix.length ≤ 6
  bits : byteToBitsLSB ds = suffix ++ true :: List.replicate (7 - suffix.length) false
  bits_last : byteToBitsLSB (ds ||| 0x80) =
    suffix ++ true :: (List.replicate (6 - suffix.length) false ++ [true])

theorem bytesToBitsLSB_pad (rate : Nat) (hr : Rate rate) (ds : UInt8) (suffix : List Bool)
    (hds : DomainByte ds suffix) (m : ByteArray) :
    bytesToBitsLSB (pad rate ds m).data.toList =
      (bytesToBitsLSB m.data.toList ++ suffix) ++
        Sponge.pad101 (8 * rate) (8 * m.size + suffix.length) := by
  have hs := hds.length_le
  have hpos : 0 < rate := by rcases hr with h | h | h | h | h <;> omega
  have hlt := Nat.mod_lt m.size hpos
  unfold pad Sponge.pad101
  dsimp only
  split
  · next hq =>
    have hj : (8 * rate - (8 * m.size + suffix.length + 2) % (8 * rate)) % (8 * rate) =
        6 - suffix.length := by
      rcases hr with h | h | h | h | h <;> subst h <;> omega
    simp only [ByteArray.data_push, Array.toList_push, bytesToBitsLSB_append,
      bytesToBitsLSB_cons, bytesToBitsLSB_nil, List.append_nil, hds.bits_last, hj,
      List.append_assoc, List.cons_append, List.nil_append]
  · next hq =>
    have hj : (8 * rate - (8 * m.size + suffix.length + 2) % (8 * rate)) % (8 * rate) =
        7 - suffix.length + 8 * (rate - m.size % rate - 2) + 7 := by
      rcases hr with h | h | h | h | h <;> subst h <;> omega
    simp only [ByteArray.data_push, ByteArray.data_append, Array.toList_push,
      Array.toList_append, ByteArray.zeros, Array.toList_replicate, bytesToBitsLSB_append,
      bytesToBitsLSB_cons, bytesToBitsLSB_nil, List.append_nil, hds.bits,
      bytesToBitsLSB_replicate_zero, hj, List.append_assoc, List.cons_append, List.nil_append,
      show byteToBitsLSB 0x80 = List.replicate 7 false ++ [true] from rfl]
    have e : ∀ a b : Nat, List.replicate a false ++ (List.replicate b false ++
        (List.replicate 7 false ++ [true])) = List.replicate (a + b + 7) false ++ [true] := by
      intro a b
      rw [← List.append_assoc, ← List.append_assoc, List.replicate_append_replicate,
        List.replicate_append_replicate]
    rw [e]

theorem size_pad (rate : Nat) (hr : Rate rate) (ds : UInt8) (m : ByteArray) :
    (pad rate ds m).size % rate = 0 := by
  have hpos : 0 < rate := by rcases hr with h | h | h | h | h <;> omega
  have hlt := Nat.mod_lt m.size hpos
  unfold pad
  dsimp only
  split
  · next hq =>
    simp only [ByteArray.size_push]
    rcases hr with h | h | h | h | h <;> subst h <;> omega
  · next hq =>
    have hz : ∀ n, (ByteArray.zeros n).size = n := fun n => by
      simp [ByteArray.zeros, ByteArray.size]
    simp only [ByteArray.size_push, ByteArray.size_append, hz]
    rcases hr with h | h | h | h | h <;> subst h <;> omega

/-! ### The sponge -/

theorem data_extract_zero (b : ByteArray) (d : Nat) :
    (b.extract 0 d).data.toList = b.data.toList.take d := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract, List.drop_zero, Nat.sub_zero]

/-- The byte-level Keccak sponge computes KECCAK[c], for `c = 1600 − 8 · rate`, on the message
bits followed by the domain-separation suffix. -/
theorem sponge_eq (rate : Nat) (hr : Rate rate) (ds : UInt8) (suffix : List Bool)
    (hds : DomainByte ds suffix) (m : ByteArray) (d : Nat) :
    bytesToBitsLSB (sponge rate ds m d).data.toList =
      Reference.keccak (1600 - 8 * rate) (bytesToBitsLSB m.data.toList ++ suffix) (8 * d) := by
  have hpos : 0 < rate := by rcases hr with h | h | h | h | h <;> omega
  have h8 : rate % 8 = 0 := by rcases hr with h | h | h | h | h <;> subst h <;> rfl
  have h200 : rate ≤ 200 := by rcases hr with h | h | h | h | h <;> omega
  unfold sponge Reference.keccak Sponge.sponge
  simp only []
  rw [show 1600 - (1600 - 8 * rate) = 8 * rate by omega, List.length_append,
    length_bytesToBitsLSB, Array.length_toList, ByteArray.size_data,
    ← bytesToBitsLSB_pad rate hr ds suffix hds]
  set p := pad rate ds m
  set N := p.size / rate
  have hsize : p.data.toList.length = N * rate := by
    rw [Array.length_toList, ByteArray.size_data]
    exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (size_pad rate hr ds m))).symm
  rw [chunks_bytesToBitsLSB _ rate N rfl hpos _ hsize, Sponge.absorb, List.foldl_map,
    ← toString_toState_zeros,
    foldl_hom_of_mem (fun a => (toState a).toString) (fun a i => absorbBlock rate a p (i * rate))]
  · have hk : max 1 ((d + rate - 1) / rate) = max 1 ((8 * d + 8 * rate - 1) / (8 * rate)) := by
      rcases hr with h | h | h | h | h <;> subst h <;> omega
    rw [data_extract_zero, bytesToBitsLSB_take, bytesToBitsLSB_squeeze rate h8 h200,
      show bytesToBitsLSB ByteArray.empty.data.toList = [] from rfl, List.nil_append, hk]
  · intro a i hi
    rw [List.mem_range] at hi
    have : (i + 1) * rate ≤ N * rate := Nat.mul_le_mul_right _ hi
    rw [Nat.succ_mul] at this
    rw [toString_absorbBlock rate h8 h200 a p (i * rate) (by
      rw [Array.length_toList, ByteArray.size_data] at hsize; omega)]

theorem rate_144 : Rate 144 := by unfold Rate; decide
theorem rate_136 : Rate 136 := by unfold Rate; decide
theorem rate_104 : Rate 104 := by unfold Rate; decide
theorem rate_72 : Rate 72 := by unfold Rate; decide
theorem rate_168 : Rate 168 := by unfold Rate; decide

/-- The SHA-3 domain byte: suffix `01`. -/
theorem domainByte_sha3 : DomainByte 0x06 [false, true] := ⟨by decide, by decide, by decide⟩
/-- The SHAKE domain byte: suffix `1111`. -/
theorem domainByte_shake : DomainByte 0x1F [true, true, true, true] :=
  ⟨by decide, by decide, by decide⟩
/-- The Keccak domain byte: no suffix. -/
theorem domainByte_keccak : DomainByte 0x01 [] := ⟨by decide, by decide, by decide⟩

/-! ### Byte strings as bit strings are injective -/

theorem bitsToNatLE_byteToBitsLSB (b : UInt8) : bitsToNatLE (byteToBitsLSB b) = b.toNat := by
  have h : ∀ n : Fin 256, bitsToNatLE (byteToBitsLSB (UInt8.ofNat n.val)) = n.val := by
    decide +kernel
  have := h ⟨b.toNat, b.toNat_lt⟩
  rwa [UInt8.ofNat_toNat] at this

theorem byteToBitsLSB_injective {a b : UInt8} (h : byteToBitsLSB a = byteToBitsLSB b) :
    a = b := by
  have := congrArg bitsToNatLE h
  rw [bitsToNatLE_byteToBitsLSB, bitsToNatLE_byteToBitsLSB] at this
  exact UInt8.toNat_inj.1 this

theorem bytesToBitsLSB_injective {l₁ l₂ : List UInt8}
    (h : bytesToBitsLSB l₁ = bytesToBitsLSB l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b l₂ =>
      have := congrArg List.length h
      simp at this
      omega
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      have := congrArg List.length h
      simp at this
    | cons b l₂ =>
      rw [bytesToBitsLSB_cons, bytesToBitsLSB_cons] at h
      obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp)
      rw [byteToBitsLSB_injective h₁, ih h₂]

end Hash.Keccak.Equiv

/-! ### The functions of FIPS 202 and Keccak-256 -/

namespace Hash.Keccak

theorem sha3x224_eq (m : ByteArray) :
    bytesToBitsLSB (Hash.sha3x224 m).data.toList =
      Reference.sha3x224 (bytesToBitsLSB m.data.toList) :=
  Equiv.sponge_eq 144 Equiv.rate_144 _ _ Equiv.domainByte_sha3 m 28

theorem sha3x256_eq (m : ByteArray) :
    bytesToBitsLSB (Hash.sha3x256 m).data.toList =
      Reference.sha3x256 (bytesToBitsLSB m.data.toList) :=
  Equiv.sponge_eq 136 Equiv.rate_136 _ _ Equiv.domainByte_sha3 m 32

theorem sha3x384_eq (m : ByteArray) :
    bytesToBitsLSB (Hash.sha3x384 m).data.toList =
      Reference.sha3x384 (bytesToBitsLSB m.data.toList) :=
  Equiv.sponge_eq 104 Equiv.rate_104 _ _ Equiv.domainByte_sha3 m 48

theorem sha3x512_eq (m : ByteArray) :
    bytesToBitsLSB (Hash.sha3x512 m).data.toList =
      Reference.sha3x512 (bytesToBitsLSB m.data.toList) :=
  Equiv.sponge_eq 72 Equiv.rate_72 _ _ Equiv.domainByte_sha3 m 64

theorem shake128_eq (m : ByteArray) (d : Nat) :
    bytesToBitsLSB (Hash.shake128 m d).data.toList =
      Reference.shake128 (bytesToBitsLSB m.data.toList) (8 * d) :=
  Equiv.sponge_eq 168 Equiv.rate_168 _ _ Equiv.domainByte_shake m d

theorem shake256_eq (m : ByteArray) (d : Nat) :
    bytesToBitsLSB (Hash.shake256 m d).data.toList =
      Reference.shake256 (bytesToBitsLSB m.data.toList) (8 * d) :=
  Equiv.sponge_eq 136 Equiv.rate_136 _ _ Equiv.domainByte_shake m d

theorem keccak256_eq (m : ByteArray) :
    bytesToBitsLSB (Hash.keccak256 m).data.toList =
      Reference.keccak256 (bytesToBitsLSB m.data.toList) := by
  rw [Reference.keccak256, ← List.append_nil (bytesToBitsLSB m.data.toList)]
  exact Equiv.sponge_eq 136 Equiv.rate_136 _ _ Equiv.domainByte_keccak m 32

/-- SHAKE128 on bytes is prefix-consistent: a shorter output is a prefix of a longer one. -/
theorem shake128_prefix (m : ByteArray) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    (Hash.shake128 m d₁).data.toList = (Hash.shake128 m d₂).data.toList.take d₁ := by
  apply Equiv.bytesToBitsLSB_injective
  rw [bytesToBitsLSB_take, shake128_eq, shake128_eq,
    Reference.shake128_prefix _ (Nat.mul_le_mul_left 8 h)]

/-- SHAKE256 on bytes is prefix-consistent: a shorter output is a prefix of a longer one. -/
theorem shake256_prefix (m : ByteArray) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    (Hash.shake256 m d₁).data.toList = (Hash.shake256 m d₂).data.toList.take d₁ := by
  apply Equiv.bytesToBitsLSB_injective
  rw [bytesToBitsLSB_take, shake256_eq, shake256_eq,
    Reference.shake256_prefix _ (Nat.mul_le_mul_left 8 h)]

end Hash.Keccak
