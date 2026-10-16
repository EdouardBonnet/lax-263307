import Lax263307.ComponentCuts
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.ComponentCuts

open Lax263307.LinearRelaxation RelaxationAlgebra

theorem indicator_cut {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ)
    (C : Finset (Fin n)) (u : ℕ) (bound : IsIndependenceBound G C u)
    (A : Finset (Fin n)) (size : A.card ≤ r)
    (I : Finset (Fin n)) (independent : G.IsIndepSet (I : Set (Fin n))) :
    ∑ v ∈ C, value (indicator r I) (insert v A) ≤
      (u : ℝ) * value (indicator r I) A := by
  rw [indicator_sum I A C (by omega), indicator_value I A (by omega)]
  by_cases hAI : A ⊆ I
  · simp only [if_pos hAI, mul_one]
    exact_mod_cast bound (C ∩ I) Finset.inter_subset_left
      (independent_subset G independent Finset.inter_subset_right)
  · simp [hAI]

theorem cut_convex {n r : ℕ} (A C : Finset (Fin n)) (u : ℕ) :
    Convex ℝ {z : MomentVector n r |
      ∑ v ∈ C, value z (insert v A) ≤ (u : ℝ) * value z A} := by
  intro y hy z hz a b ha hb _
  simp only [Set.mem_ofPred_eq] at hy hz ⊢
  simp_rw [value_combination, Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    a * (∑ v ∈ C, value y (insert v A)) + b * (∑ v ∈ C, value z (insert v A)) ≤
      a * ((u : ℝ) * value y A) + b * ((u : ℝ) * value z A) :=
        add_le_add (mul_le_mul_of_nonneg_left hy ha) (mul_le_mul_of_nonneg_left hz hb)
    _ = _ := by ring

/--
---
conclusion: Lax263307.ComponentCuts.valid_cut
---
The recursive independence bound yields an inequality valid throughout
the exact independent-set hull.

# Proof strategy

On an indicator vector the left side is zero if the conditioning set is
absent, and otherwise equals the size of the intersection with `C`.
The upper bound applies to this independent intersection. The halfspace
is convex, so the inequality extends to the entire hull.
-/
theorem valid_cut {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (C : Finset (Fin n)) (u : ℕ) (bound : IsIndependenceBound G C u)
    (A : Finset (Fin n)) (size : A.card ≤ r)
    (z : MomentVector n r) (member : z ∈ independentSetHull G k r) :
    ∑ v ∈ C, value z (insert v A) ≤ (u : ℝ) * value z A := by
  apply convexHull_min (t := {z | ∑ v ∈ C, value z (insert v A) ≤
    (u : ℝ) * value z A}) ?_ (cut_convex A C u) member
  rintro y ⟨I, hI, _, rfl⟩
  exact indicator_cut G r C u bound A size I hI


end Lax263307Proofs.ComponentCuts
