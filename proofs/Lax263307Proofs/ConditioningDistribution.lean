import Lax263307.ConditioningDistribution
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.ConditioningDistribution

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution RelaxationAlgebra

/--
---
conclusion: Lax263307.ConditioningDistribution.distribution_identities
---
The first and second conditioned moments define the probability
distributions used by the entropy argument.

# Proof strategy

The mass equation at `A` normalizes the vertex distribution; the same
equation at `A ∪ {v}` gives the marginal of the joint distribution.
Symmetry is commutativity of insertion. A set containing the endpoints
of an edge has zero moment. Clearing positive denominators gives the
conditional-probability identity.
-/
theorem distribution_identities {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A : Finset (Fin n)) (size : A.card < r) (positive : 0 < value y A)
    (target_positive : 0 < k) :
    (∀ v, 0 ≤ marginal y A k v) ∧
    (∑ v : Fin n, marginal y A k v) = 1 ∧
    (∀ u v, 0 ≤ joint y A k u v) ∧
    (∀ u v, joint y A k u v = joint y A k v u) ∧
    (∀ v, (∑ u : Fin n, joint y A k u v) = marginal y A k v) ∧
    (∀ u v, G.Adj u v → joint y A k u v = 0) ∧
    (∀ u v, 0 < marginal y A k v →
      marginal y (insert v A) k u = joint y A k u v / marginal y A k v) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast target_positive
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hk
  have hA0 : value y A ≠ 0 := ne_of_gt positive
  have invariants := Lax263307.ConditionedCosts.conditioning_invariants
    G k r y feasible A (by omega) positive
  have hsize (v : Fin n) : (insert v A).card ≤ r + 1 := by
    have := Finset.card_insert_le v A
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact div_nonneg (invariants.1 v).1 hk.le
  · simp_rw [marginal, ← Finset.sum_div]
    rw [invariants.2.1, div_self hk0]
  · intro u v
    have hnonneg : 0 ≤ value y (insert u (insert v A)) := by
      rw [value_of_size y _ (insert_size _ (hsize v) u)]
      exact (feasible.bounds _).1
    exact div_nonneg hnonneg (mul_nonneg (sq_nonneg _) positive.le)
  · intro u v
    simp only [joint, Finset.insert_comm]
  · intro v
    simp_rw [joint, ← Finset.sum_div]
    rw [feasible.mass (insert v A) (hsize v)]
    dsimp [marginal, conditioned]
    field_simp
  · intro u v huv
    have hnot : ¬G.IsIndepSet (↑(insert u (insert v A)) : Set (Fin n)) := by
      intro hi
      exact hi (by simp) (by simp) huv.ne huv
    have hz := feasible.vanishes
      ⟨insert u (insert v A), insert_size _ (hsize v) u⟩ hnot
    rw [joint, value_of_size y _ (insert_size _ (hsize v) u), hz, zero_div]
  · intro u v hv
    have hv0 : value y (insert v A) ≠ 0 := by
      have hcost : 0 < conditioned y A v := (div_pos_iff_of_pos_right hk).1 hv
      exact ne_of_gt (invariants.2.2.2 v hcost)
    dsimp [marginal, conditioned, joint]
    field_simp

end Lax263307Proofs.ConditioningDistribution
