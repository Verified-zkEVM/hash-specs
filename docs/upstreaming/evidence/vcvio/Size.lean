import Hash
open Hash

theorem length_keccak (c : Nat) (hc : c < 1600) (N : List Bool) (d : Nat) :
    (Keccak.Reference.keccak c N d).length = d := by
  unfold Keccak.Reference.keccak Sponge.sponge
  have hf : ∀ S, (Keccak.keccakP 6 24 S).length = 1600 := fun S => by
    rw [Keccak.length_keccakP 6 24 (by decide)]; rfl
  rw [List.length_take, Sponge.length_squeeze _ _ 1600 (by omega) hf _
    (Sponge.length_absorb _ 1600 _ hf _ List.length_replicate _)]
  have := Sponge.le_blocks_mul (r := 1600 - c) d (by omega)
  omega

theorem shake256_size (m : ByteArray) (d : Nat) : (Hash.shake256 m d).size = d := by
  have h := congrArg List.length (Hash.Keccak.shake256_eq m d)
  simp only [length_bytesToBitsLSB, Array.length_toList, ByteArray.size_data] at h
  rw [Keccak.Reference.shake256, length_keccak _ (by decide)] at h
  omega

theorem sha3x256_size (m : ByteArray) : (Hash.sha3x256 m).size = 32 := by
  have h := congrArg List.length (Hash.Keccak.sha3x256_eq m)
  simp only [length_bytesToBitsLSB, Array.length_toList, ByteArray.size_data] at h
  rw [Keccak.Reference.sha3x256, length_keccak _ (by decide)] at h
  omega

theorem take_toList_shake256 (x : ByteArray) {n m : ℕ} (hnm : n ≤ m) :
    (Hash.shake256 x m).data.toList.take n = (Hash.shake256 x n).data.toList :=
  (Hash.Keccak.shake256_prefix x hnm).symm
