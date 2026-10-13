import Lax263307.AlgorithmParameters
import Mathlib.Tactic

namespace Lax263307Proofs.AlgorithmParameters

open Lax263307.AlgorithmParameters

theorem sparsity_positive {a K B n D : ℕ} (hK : 0 < K) : 0 < sparsity a K B n D := by
  unfold sparsity targetThreshold
  positivity

/--
---
conclusion: Lax263307.AlgorithmParameters.budgets
---
The load clears the accuracy denominator exactly. Sparsity is twice the
target threshold, and the level is the sparsity times the binary-log bound.
-/
theorem budgets {a K B n D k : ℕ} (hK : 0 < K) (hB : 0 < B)
    (hD : 4 ≤ D) (large : cutoff a K B n D < k) :
    0 < load B n D ∧ 0 < sparsity a K B n D ∧ 0 < level a K B n D ∧
      0 < (1 / (D : ℝ)) ∧ (1 / (D : ℝ)) ≤ 1 / 4 ∧
      12 * (B : ℝ) * ((Nat.log2 (2 * n) : ℝ) + 1) ≤
        (1 / (D : ℝ)) * load B n D ∧
      (sparsity a K B n D : ℝ) * ((Nat.log2 n : ℝ) + 1) ≤ level a K B n D ∧
      (K : ℝ) * ((load B n D : ℝ) + 1) ^ (4 * a + 2) ≤ k ∧
      (2 * K : ℝ) * ((load B n D : ℝ) + 1) ^ (4 * a + 2) ≤ sparsity a K B n D := by
  have hp := sparsity_positive (a := a) (B := B) (n := n) (D := D) hK
  have hD' : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hD4 : (4 : ℝ) ≤ D := by exact_mod_cast hD
  have ht : targetThreshold a K B n D ≤ k :=
    (le_max_left _ _).trans large.le
  refine ⟨?_, hp, ?_, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · unfold load logarithm
    positivity
  · unfold level
    positivity
  · exact one_div_le_one_div_of_le (by norm_num) hD4
  · have heq : (1 / (D : ℝ)) * load B n D =
        12 * (B : ℝ) * ((Nat.log2 (2 * n) : ℝ) + 1) := by
      simp only [load, logarithm, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      field_simp
    exact heq.ge
  · simp [level, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  · exact_mod_cast ht
  · simp only [sparsity, targetThreshold, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    ring_nf
    exact le_rfl

/--
---
conclusion: Lax263307.AlgorithmParameters.conditioning_floor
---
The integer floor denominator is exactly the denominator of the heavy
conditioning probability floor; rational casts preserve its reciprocal power.
-/
theorem conditioning_floor (a K B n D : ℕ) :
    (momentFloor a K B n D : ℝ) =
      Lax263307.HeavyConditioning.probabilityFloor n (sparsity a K B n D) ^ level a K B n D := by
  unfold momentFloor
  push_cast
  simp only [floorDenominator, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    Lax263307.HeavyConditioning.probabilityFloor]
  rw [one_div_pow]

/--
---
conclusion: Lax263307.AlgorithmParameters.protected_radius
---
The protected-radius denominator is positive. A power of two with exponent
that denominator plus two is larger than the denominator itself.
-/
theorem protected_radius {a K B n D : ℕ} (hK : 0 < K) (hn : 0 < n) (hD : 0 < D) :
    2 ≤ precision a K B n D ∧
      ((2 : ℝ) ^ precision a K B n D)⁻¹ ≤
        (momentFloor a K B n D : ℝ) /
          (256 * (Lax263307.MomentLP.dimension n (level a K B n D) : ℝ) * (n : ℝ) ^ 2 * (D : ℝ) ^ 2) := by
  have hp := sparsity_positive (a := a) (B := B) (n := n) (D := D) hK
  have hN : 0 < Lax263307.MomentLP.dimension n (level a K B n D) :=
    Lax263307.CoordinateCatalog.catalog_positive n _
  have hQ : 0 < floorDenominator a K B n D := by unfold floorDenominator; positivity
  have hM : 0 < radiusDenominator a K B n D := by unfold radiusDenominator; positivity
  have hM' : (0 : ℝ) < radiusDenominator a K B n D := by exact_mod_cast hM
  have hpow : radiusDenominator a K B n D ≤ 2 ^ precision a K B n D := by
    exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by unfold precision; omega))
  have hpow' : (radiusDenominator a K B n D : ℝ) ≤ (2 : ℝ) ^ precision a K B n D := by
    exact_mod_cast hpow
  refine ⟨by unfold precision; omega, ?_⟩
  have heq : (momentFloor a K B n D : ℝ) /
      (256 * (Lax263307.MomentLP.dimension n (level a K B n D) : ℝ) * (n : ℝ) ^ 2 * (D : ℝ) ^ 2) =
      1 / (radiusDenominator a K B n D : ℝ) := by
    simp only [momentFloor, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast,
      radiusDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [heq]
  simpa only [one_div] using one_div_le_one_div_of_le hM' hpow'

end Lax263307Proofs.AlgorithmParameters
