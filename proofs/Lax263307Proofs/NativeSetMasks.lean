import Lax263307Proofs.NativeMasks

namespace Lax263307Proofs.NativeSetMasks

open NativeMasks

theorem outside {n : ℕ} (A : Finset (Fin n)) (j : ℕ) (hj : n≤j) : (mask A).testBit j=false := by
  rw [mask_test_bit]
  apply decide_eq_false_iff_not.mpr
  intro h
  obtain ⟨v,hv,hvj⟩ := Finset.mem_image.mp h
  have hh := v.isLt
  omega

theorem union {n : ℕ} (A C : Finset (Fin n)) : mask (A∪C)=Nat.lor (mask A) (mask C) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (A∪C)).testBit j=((mask A)|||(mask C)).testBit j
  rw [Nat.testBit_or]
  by_cases hj : j<n
  · change (mask (A∪C)).testBit (⟨j,hj⟩ : Fin n).val=_
    rw [mask_member (A∪C) ⟨j,hj⟩,mask_member A ⟨j,hj⟩,mask_member C ⟨j,hj⟩]
    by_cases hA : (⟨j,hj⟩ : Fin n)∈A <;> by_cases hC : (⟨j,hj⟩ : Fin n)∈C <;> simp [hA,hC]
  · simp only [outside _ _ (Nat.le_of_not_gt hj),Bool.or_false]

theorem inter {n : ℕ} (A C : Finset (Fin n)) : mask (A∩C)=Nat.land (mask A) (mask C) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (A∩C)).testBit j=((mask A)&&&(mask C)).testBit j
  rw [Nat.testBit_and]
  by_cases hj : j<n
  · change (mask (A∩C)).testBit (⟨j,hj⟩ : Fin n).val=_
    rw [mask_member (A∩C) ⟨j,hj⟩,mask_member A ⟨j,hj⟩,mask_member C ⟨j,hj⟩]
    by_cases hA : (⟨j,hj⟩ : Fin n)∈A <;> by_cases hC : (⟨j,hj⟩ : Fin n)∈C <;> simp [hA,hC]
  · simp only [outside _ _ (Nat.le_of_not_gt hj),Bool.and_false]

theorem sdiff {n : ℕ} (A C : Finset (Fin n)) :
    mask (A\C)=Nat.xor (mask A) (Nat.land (mask A) (mask C)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (A\C)).testBit j=((mask A)^^^((mask A)&&&(mask C))).testBit j
  rw [Nat.testBit_xor,Nat.testBit_and]
  by_cases hj : j<n
  · change (mask (A\C)).testBit (⟨j,hj⟩ : Fin n).val=_
    rw [mask_member (A\C) ⟨j,hj⟩,mask_member A ⟨j,hj⟩,mask_member C ⟨j,hj⟩]
    by_cases hA : (⟨j,hj⟩ : Fin n)∈A <;> by_cases hC : (⟨j,hj⟩ : Fin n)∈C <;> simp [hA,hC]
  · simp only [outside _ _ (Nat.le_of_not_gt hj),Bool.and_false,Bool.xor_self]

end Lax263307Proofs.NativeSetMasks
