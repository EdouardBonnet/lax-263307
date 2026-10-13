import Lax263307.PowerBagBounds
import Mathlib.Tactic

namespace Lax263307Proofs.PowerBagBounds

open Lax263307.GraphClasses Lax263307.InducedEmbeddingWidth Lax228581.Treewidth
open Lax263307.PowerBagBounds

/--
---
conclusion: Lax263307.PowerBagBounds.root_bag_bound
---
Use the integer root's defining power inequalities to bound every bag,
prove monotonicity in edge count, obtain the lower bound one, and preserve
the original power inequality.
-/
theorem root_bag_bound (C : GraphClass) (a A : ℕ) (a_positive : 0 < a) (A_positive : 0 < A)
    (class_bound : HasPowerBagBound C a A) :
    Monotone (bagBound a A) ∧ HasBagBound C (bagBound a A) ∧
      (∀ m, 1 ≤ bagBound a A m) ∧
      (∀ m, (bagBound a A m) ^ a ≤ A * (m + 1) ^ (a - 1)) := by
  have ha : a ≠ 0 := ne_of_gt a_positive
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m n hmn
    apply (Nat.le_nthRoot_iff ha).mpr
    exact (Nat.pow_nthRoot_le (Or.inl ha)).trans
      (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (Nat.succ_le_succ hmn) _))
  · intro n G hG
    obtain ⟨D, hD⟩ := class_bound n G hG
    exact ⟨D, fun i => (Nat.le_nthRoot_iff ha).mpr (hD i)⟩
  · intro m
    apply (Nat.le_nthRoot_iff ha).mpr
    simp only [one_pow]
    exact Nat.succ_le_of_lt (Nat.mul_pos A_positive (Nat.pow_pos (Nat.succ_pos m)))
  · intro m
    exact Nat.pow_nthRoot_le (Or.inl ha)


end Lax263307Proofs.PowerBagBounds
