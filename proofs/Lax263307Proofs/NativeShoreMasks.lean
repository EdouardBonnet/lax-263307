import Lax263307Proofs.NativeRestrictionOrder

namespace Lax263307Proofs.NativeShoreMasks

open Lax263307 ComputedSeparators VertexSplitting

def partialMask {r n : ℕ} (f : Fin r → Fin n) (S : Finset (Fin r)) (i : ℕ) : ℕ :=
  NativeMasks.mask ((NativeMasks.initialSet S i).image f)

theorem zero {r n : ℕ} (f : Fin r → Fin n) (S : Finset (Fin r)) : partialMask f S 0=0 := by
  simp only [partialMask,NativeMasks.prefix_zero,Finset.image_empty,NativeMasks.mask_empty]

theorem full {r n : ℕ} (f : Fin r → Fin n) (S : Finset (Fin r)) :
    partialMask f S r=NativeMasks.mask (S.image f) := by rw [partialMask,NativeMasks.prefix_full]

theorem bound {r n : ℕ} (f : Fin r → Fin n) (S : Finset (Fin r)) (i : ℕ) : partialMask f S i<2^n :=
  NativeMasks.mask_bound _

theorem step {r n : ℕ} (f : Fin r → Fin n) (S : Finset (Fin r)) (i : Fin r) :
    Nat.lor (partialMask f S i.val) ((if i∈S then 1 else 0)*2^(f i).val)=partialMask f S (i.val+1) := by
  simp only [partialMask]
  rw [NativeMasks.prefix_succ S i.val i.isLt]
  by_cases h : i∈S
  · simp only [h,if_true,one_mul,Finset.image_insert,NativeMasks.mask_insert]
  · simp [h]

theorem left_member {r : ℕ} (xs : List ℕ) (i : Fin r) :
    i∈leftShore (decodeCut (2*r) xs) ↔ xs.getD (2*i.val) 0=1 := by
  simp [leftShore,decodeCut,minus]

theorem right_member {r : ℕ} (xs : List ℕ) (i : Fin r) :
    i∈rightShore (decodeCut (2*r) xs) ↔ xs.getD (2*i.val+1) 0≠1 := by
  simp [rightShore,decodeCut,plus]

theorem orient_images {r n : ℕ} (f : Fin r → Fin n) (hf : Function.Injective f)
    (A B : Finset (Fin r)) :
    ((orient A B).1.image f,(orient A B).2.image f)=orient (A.image f) (B.image f) := by
  simp only [orient,Finset.card_image_of_injective _ hf]
  split_ifs <;> rfl

end Lax263307Proofs.NativeShoreMasks
