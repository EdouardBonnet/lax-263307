import Lax263307.WeightedProjection
import Lax263307Proofs.RoundingBounds

namespace Lax263307Proofs.WeightedProjection

open Lax263307.WeightedIndependentSet Lax263307.WeightRounding Lax263307.IndependentBlowUp
open RoundingBounds

theorem exists_optimal_set {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) :
    ∃ I : Finset (Fin n), G.IsIndepSet (I : Set (Fin n)) ∧
      ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → weight w J ≤ weight w I := by
  classical
  let S := Finset.univ.filter fun I : Finset (Fin n) => G.IsIndepSet (I : Set (Fin n))
  have hS : S.Nonempty := ⟨∅, by simp [S, SimpleGraph.IsIndepSet]⟩
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image S (weight w) hS
  refine ⟨I, (Finset.mem_filter.mp hI).2, ?_⟩
  intro J hJ
  exact hmax J (by simp [S, hJ])

theorem maximum_le_optimal {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (I : Finset (Fin n))
    (hmax : ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → weight w J ≤ weight w I) :
    maximumWeight w ≤ weight w I := by
  apply Finset.max'_le
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · simpa [weight] using hmax ∅ (by simp [SimpleGraph.IsIndepSet])
  · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ha
    simpa [weight] using hmax {v} (by simp [SimpleGraph.IsIndepSet])

theorem projection_weight_lower {n : ℕ} (w : Fin n → ℚ) (τ : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hτ : 0 < τ) (K : Finset (Vertex (roundedCopies w τ))) :
    τ * (K.card : ℚ) ≤ weight w (project K) := by
  have hcard : (K.card : ℚ) ≤ ((∑ v ∈ project K, roundedCopies w τ v : ℕ) : ℚ) := by
    exact_mod_cast Lax263307.BlowUpIndependentSets.projection_capacity (roundedCopies w τ) K
  calc
    τ * (K.card : ℚ) ≤ τ * ((∑ v ∈ project K, roundedCopies w τ v : ℕ) : ℚ) :=
      mul_le_mul_of_nonneg_left hcard hτ.le
    _ = ∑ v ∈ project K, τ * (roundedCopies w τ v : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
    _ ≤ weight w (project K) := Finset.sum_le_sum fun v _ =>
      (Lax263307.RoundingBounds.pointwise_bounds w τ hw hτ v).1

/--
---
conclusion: Lax263307.WeightedProjection.approximation_transfer
---
The projected independent set meets the full weighted approximation guarantee.

# Proof strategy

Choose an optimum only for analysis. Its weight is at least the maximum
vertex weight, so rounding loses at most an `ε/2` fraction of that optimum.
Lift this comparison set and use the unweighted `ε/2` approximation.
Projection has weight at least the scale times the number of selected copies.
The combined factor `(1-ε/2)²` is at least `1-ε`.
-/
theorem approximation_transfer {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (nonnegative : ∀ v, 0 ≤ w v) (positive_order : 0 < n)
    (positive_accuracy : 0 < ε) (accuracy_lt_one : ε < 1)
    (positive_maximum : 0 < maximumWeight w)
    (K : Finset (Vertex (copies w ε)))
    (approximation : IsCardinalityApproximation G (copies w ε) (ε / 2) K) :
    IsApproximation G w ε (project K) := by
  obtain ⟨I, hI, hmax⟩ := exists_optimal_set G w
  have hW := maximum_le_optimal G w I hmax
  have hopt : 0 ≤ weight w I := (maximum_nonnegative w).trans hW
  have hτ := scale_positive w ε positive_order positive_accuracy positive_maximum
  have hρ : 0 ≤ 1 - ε / 2 := by linarith
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt positive_order
  have hcardI : (I.card : ℚ) ≤ n := by
    exact_mod_cast (show I.card ≤ n from by simpa using Finset.card_le_univ I)
  have hscale : (n : ℚ) * scale w ε = (ε / 2) * maximumWeight w := by
    unfold scale
    field_simp
  have herror : (I.card : ℚ) * scale w ε ≤ (ε / 2) * weight w I := by
    calc
      (I.card : ℚ) * scale w ε ≤ (n : ℚ) * scale w ε :=
        mul_le_mul_of_nonneg_right hcardI hτ.le
      _ = (ε / 2) * maximumWeight w := hscale
      _ ≤ (ε / 2) * weight w I := mul_le_mul_of_nonneg_left hW (by positivity)
  have hloss := Lax263307.RoundingBounds.set_rounding_loss
    w (scale w ε) nonnegative hτ I
  change weight w I - (I.card : ℚ) * scale w ε ≤
    scale w ε * ((∑ v ∈ I, copies w ε v : ℕ) : ℚ) at hloss
  rw [← Lax263307.BlowUpIndependentSets.lift_cardinality (copies w ε) I] at hloss
  have hrounded : (1 - ε / 2) * weight w I ≤
      scale w ε * ((lift (copies w ε) I).card : ℚ) := by linarith
  have hcompare := approximation.2 (lift (copies w ε) I)
    (Lax263307.BlowUpIndependentSets.lift_independent G (copies w ε) I hI)
  have hscaled := mul_le_mul_of_nonneg_left hcompare hτ.le
  have hweight := projection_weight_lower w (scale w ε) nonnegative hτ K
  have hcombined : (1 - ε / 2) ^ 2 * weight w I ≤ weight w (project K) := by
    calc
      (1 - ε / 2) ^ 2 * weight w I = (1 - ε / 2) * ((1 - ε / 2) * weight w I) := by ring
      _ ≤ (1 - ε / 2) * (scale w ε * ((lift (copies w ε) I).card : ℚ)) :=
        mul_le_mul_of_nonneg_left hrounded hρ
      _ = scale w ε * ((1 - ε / 2) * ((lift (copies w ε) I).card : ℚ)) := by ring
      _ ≤ scale w ε * (K.card : ℚ) := hscaled
      _ ≤ weight w (project K) := hweight
  have hfactor : 1 - ε ≤ (1 - ε / 2) ^ 2 := by nlinarith [sq_nonneg ε]
  have hmain := (mul_le_mul_of_nonneg_right hfactor hopt).trans hcombined
  refine ⟨Lax263307.BlowUpIndependentSets.project_independent G (copies w ε) K approximation.1, ?_⟩
  intro J hJ
  exact (mul_le_mul_of_nonneg_left (hmax J hJ) (by linarith)).trans hmain

end Lax263307Proofs.WeightedProjection
