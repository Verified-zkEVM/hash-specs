import Hash
#print axioms Hash.Keccak.keccak256_eq
#print axioms Hash.SHA2.sha256_eq
#print axioms Hash.BLAKE2.blake2bF_eq
#print axioms Hash.Keccak.Equiv.toState_keccakF
#check @Hash.Keccak.Fast.keccakF
#check @UInt64.ofBitVec
#check @UInt8.ofBitVec
example : Hash.SHA2.sha256.w = 32 := rfl
example : Hash.BLAKE2.blake2bParams.w = 64 := rfl
