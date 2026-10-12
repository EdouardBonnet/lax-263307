import Lax263307.PositiveWeights
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.PositiveWeights

open Lax263307.WeightedIndependentSet Lax263307.PositiveWeights RelaxationAlgebra

theorem clipped_weight_eq {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) :
    weight w (discardNonpositive w I) = weight (positiveWeights w) I := by
  simp only [weight, discardNonpositive, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : 0 < w v
  · simp [h, positiveWeights, max_eq_left h.le]
  · simp [h, positiveWeights, max_eq_right (not_lt.mp h)]

/--
---
conclusion: Lax263307.PositiveWeights.signed_weight_transfer
---
Clipping negative weights and removing nonpositive returned vertices
preserves the requested approximation factor.

# Proof strategy

The filtered output has exactly the clipped weight of the original output.
Clipping can only increase a comparison set's weight, and filtering preserves
independence. Multiply the comparison by the nonnegative approximation factor.
-/
theorem signed_weight_transfer {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (_accuracy_nonnegative : 0 ≤ ε) (accuracy_le_one : ε ≤ 1)
    (I : Finset (Fin n)) (approximation : IsApproximation G (positiveWeights w) ε I) :
    IsApproximation G w ε (discardNonpositive w I) := by
  refine ⟨independent_subset G approximation.1 (Finset.filter_subset _ _), ?_⟩
  intro J hJ
  rw [clipped_weight_eq]
  have hweight : weight w J ≤ weight (positiveWeights w) J :=
    Finset.sum_le_sum fun v _ => le_max_left (w v) 0
  exact (mul_le_mul_of_nonneg_left hweight (sub_nonneg.mpr accuracy_le_one)).trans
    (approximation.2 J hJ)

/--
---
conclusion: Lax263307.PositiveWeights.nonpositive_case
---
The empty independent set is optimal when all weights are nonpositive.

# Proof strategy

Every comparison set has nonpositive total weight. Multiplication by the
nonnegative approximation factor preserves this upper bound by zero.
-/
theorem nonpositive_case {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (nonpositive : ∀ v, w v ≤ 0) (ε : ℚ) (_accuracy_nonnegative : 0 ≤ ε)
    (accuracy_le_one : ε ≤ 1) : IsApproximation G w ε ∅ := by
  refine ⟨by simp [SimpleGraph.IsIndepSet], ?_⟩
  intro J _
  have hsum : weight w J ≤ 0 := Finset.sum_nonpos fun v _ => nonpositive v
  simpa [weight] using mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr accuracy_le_one) hsum

end Lax263307Proofs.PositiveWeights
