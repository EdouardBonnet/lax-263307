import Lax263307.RelaxationFeasibility
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.RelaxationFeasibility

open Lax263307.LinearRelaxation RelaxationAlgebra

/--
---
conclusion: Lax263307.RelaxationFeasibility.indicator_feasible
---
Every independent-set indicator satisfies the relaxation constraints.

# Proof strategy

Inclusion indicators are monotone, and every subset of an independent set
is independent. The mass equation counts the vertices of the selected set
when the conditioning set is included, and is zero otherwise.
-/
theorem indicator_feasible {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (I : Finset (Fin n)) (independent : G.IsIndepSet (I : Set (Fin n)))
    (cardinality : I.card = k) : IsFeasible G k r (indicator r I) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [value, indicator]
  · intro A
    dsimp [indicator]
    split_ifs <;> norm_num
  · intro A hA v
    rw [indicator_value I _ (insert_size A hA v),
      indicator_value I A (by omega)]
    by_cases hAI : A ⊆ I
    · simp only [if_pos hAI]
      split_ifs <;> norm_num
    · have hnot : ¬insert v A ⊆ I := fun h => hAI ((Finset.subset_insert v A).trans h)
      simp [hAI, hnot]
  · intro A hA
    have hnot : ¬A.val ⊆ I := fun h => hA (independent_subset G independent h)
    simp [indicator, hnot]
  · intro A hA
    rw [indicator_sum I A Finset.univ hA, indicator_value I A (by omega)]
    simp [cardinality]

theorem feasible_convex {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ) :
    Convex ℝ {y : MomentVector n r | IsFeasible G k r y} := by
  intro y hy z hz a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [value_combination, hy.normalized, hz.normalized]
    simpa using hab
  · intro A
    change 0 ≤ a * y A + b * z A ∧ a * y A + b * z A ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg ha (hy.bounds A).1) (mul_nonneg hb (hz.bounds A).1)
    · calc
        a * y A + b * z A ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hy.bounds A).2 ha)
            (mul_le_mul_of_nonneg_left (hz.bounds A).2 hb)
        _ = 1 := by simpa using hab
  · intro A hA v
    rw [value_combination, value_combination]
    exact add_le_add (mul_le_mul_of_nonneg_left (hy.monotone A hA v) ha)
      (mul_le_mul_of_nonneg_left (hz.monotone A hA v) hb)
  · intro A hA
    change a * y A + b * z A = 0
    simp [hy.vanishes A hA, hz.vanishes A hA]
  · intro A hA
    simp_rw [value_combination, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hy.mass A hA, hz.mass A hA]
    ring

/--
---
conclusion: Lax263307.RelaxationFeasibility.hull_feasible
---
The exact independent-set hull satisfies all relaxation constraints.

# Proof strategy

The feasible set is convex because all five constraint families are
linear. It contains every independent-set indicator, hence their convex hull.
-/
theorem hull_feasible {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) (member : y ∈ independentSetHull G k r) :
    IsFeasible G k r y := by
  apply convexHull_min (t := {y | IsFeasible G k r y}) ?_ (feasible_convex G k r) member
  rintro z ⟨I, hI, hk, rfl⟩
  exact Lax263307.RelaxationFeasibility.indicator_feasible G k r I hI hk

end Lax263307Proofs.RelaxationFeasibility
