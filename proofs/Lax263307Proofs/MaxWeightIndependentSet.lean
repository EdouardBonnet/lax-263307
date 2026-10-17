import Lax263307.MaxWeightIndependentSet
import Lax213208.Approximation
import Mathlib.Tactic

namespace Lax263307Proofs.MaxWeightIndependentSet

open Lax263307 Lax263307.MaxWeightIndependentSet WeightedIndependentSet IndependentSetEncoding

/-- The existing algorithm receives the canonical instance followed by accuracy. -/
theorem input_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (ε : ℚ) :
    encodeInput G w ε = encodeInstance G w ++ encodeRational ε := by
  classical
  simp only [encodeInput, encodeInstance, encodeParameters, List.append_assoc]
  congr!

theorem nonnegative {n : ℕ} {G : SimpleGraph (Fin n)} {w : Fin n → ℚ}
    {ε : ℚ} {I : Finset (Fin n)} (h : IsApproximation G w ε I) : 0 ≤ weight w I := by
  simpa [weight] using h.2 ∅ (by simp)

/-- Integer precision in lax-213208 corresponds to accuracy `1/(k+1)` here. -/
theorem approximation {n k : ℕ} (hk : 0 < k) {G : SimpleGraph (Fin n)}
    {w : Fin n → ℚ} {I : Finset (Fin n)}
    (h : IsApproximation G w (1/(k+1)) I) :
    Lax213208.Approximation.IsApproximation MaxWeightIndependentSet (1+1/(k:ℝ))
      (⟨n, G, w⟩ : Instance) (⟨n, I⟩ : Solution) := by
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hI : (0:ℝ) ≤ weight w I := by exact_mod_cast nonnegative h
  refine ⟨le_add_of_nonneg_right (by positivity),
    ⟨I, rfl, h.1⟩, ?_⟩
  rintro z ⟨J, rfl, hJ⟩
  have hc := h.2 J hJ
  have hcR : (1-1/((k:ℝ)+1)) * (weight w J : ℝ)
      ≤ (weight w I : ℝ) := by
    have ht := (Rat.cast_le (K := ℝ)).mpr hc
    push_cast at ht
    exact ht
  have he : (1+1/(k:ℝ))*(1-1/((k:ℝ)+1)) = 1 := by
    field_simp
    ring
  have hr : 0 ≤ 1+1/(k:ℝ) := by positivity
  have hc' := mul_le_mul_of_nonneg_left hcR hr
  rw [← mul_assoc, he, one_mul] at hc'
  change (objectiveValue ⟨n,G,w⟩ ⟨n,J⟩ : ℝ) ≤
    (1+1/(k:ℝ)) * (objectiveValue ⟨n,G,w⟩ ⟨n,I⟩ : ℝ)
  simpa [objectiveValue, Real.coe_toNNReal', max_eq_left hI] using
    (max_le hc' (mul_nonneg hr hI))

end Lax263307Proofs.MaxWeightIndependentSet
