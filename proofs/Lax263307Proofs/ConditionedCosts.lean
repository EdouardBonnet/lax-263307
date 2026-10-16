import Lax263307.ConditionedCosts
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.ConditionedCosts

open Lax263307.LinearRelaxation RelaxationAlgebra

/--
---
conclusion: Lax263307.ConditionedCosts.conditioning_invariants
---
Conditioning preserves the unit-interval bounds and total mass, fixes the
chosen vertices to one, and preserves positivity at every positive-cost step.

# Proof strategy

Divide the monotonicity inequalities and mass equation by the positive
conditioning moment. Inserting a vertex already in the conditioning set
does not change the set.
-/
theorem conditioning_invariants {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A : Finset (Fin n)) (size : A.card ≤ r) (positive : 0 < value y A) :
    (∀ v, 0 ≤ conditioned y A v ∧ conditioned y A v ≤ 1) ∧
    (∑ v : Fin n, conditioned y A v) = k ∧
    (∀ v ∈ A, conditioned y A v = 1) ∧
    (∀ v, 0 < conditioned y A v → 0 < value y (insert v A)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    have hsize := insert_size A (show A.card ≤ r + 1 by omega) v
    have hnonneg : 0 ≤ value y (insert v A) := by
      rw [value_of_size y _ hsize]
      exact (feasible.bounds _).1
    exact ⟨div_nonneg hnonneg positive.le,
      (div_le_one positive).2 (feasible.monotone A (by omega) v)⟩
  · simp_rw [conditioned, ← Finset.sum_div]
    rw [feasible.mass A (by omega)]
    exact mul_div_cancel_right₀ _ (ne_of_gt positive)
  · intro v hv
    simp [conditioned, Finset.insert_eq_of_mem hv, ne_of_gt positive]
  · intro v hv
    exact (div_pos_iff_of_pos_right positive).1 hv

end Lax263307Proofs.ConditionedCosts
