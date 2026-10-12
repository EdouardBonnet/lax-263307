import Lax263307.RoundingBounds
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.RoundingBounds

open Lax263307.WeightedIndependentSet Lax263307.WeightRounding

theorem maximum_nonnegative {n : ℕ} (w : Fin n → ℚ) : 0 ≤ maximumWeight w := by
  exact (insert 0 (Finset.univ.image w)).le_max' 0 (by simp)

theorem le_maximum {n : ℕ} (w : Fin n → ℚ) (v : Fin n) : w v ≤ maximumWeight w := by
  exact (insert 0 (Finset.univ.image w)).le_max' (w v) (by simp)

theorem scale_positive {n : ℕ} (w : Fin n → ℚ) (ε : ℚ)
    (hn : 0 < n) (hε : 0 < ε) (hW : 0 < maximumWeight w) : 0 < scale w ε := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  exact div_pos (mul_pos hε hW) (mul_pos (by norm_num) hnQ)

/--
---
conclusion: Lax263307.RoundingBounds.pointwise_bounds
---
Floor rounding bounds each original vertex weight between its rounded
weight and one further scaling unit.

# Proof strategy

Apply the lower and upper floor inequalities to `w_v / τ` and multiply
by the positive scaling unit.

# Attribution

Bonnet–Chang, proof of Theorem 2 in Section 6.
-/
theorem pointwise_bounds {n : ℕ} (w : Fin n → ℚ) (τ : ℚ)
    (nonnegative : ∀ v, 0 ≤ w v) (positive_scale : 0 < τ) :
    ∀ v, τ * (roundedCopies w τ v : ℚ) ≤ w v ∧
      w v - τ ≤ τ * (roundedCopies w τ v : ℚ) := by
  intro v
  have hupper := (le_div_iff₀ positive_scale).1
    (Nat.floor_le (div_nonneg (nonnegative v) positive_scale.le))
  have hlower := (div_lt_iff₀ positive_scale).1 (Nat.lt_floor_add_one (w v / τ))
  dsimp [roundedCopies]
  constructor <;> nlinarith

/--
---
conclusion: Lax263307.RoundingBounds.set_rounding_loss
---
The total weight lost by rounding a set is at most one scaling unit
per selected vertex.

# Proof strategy

Sum the pointwise lower bounds and collect the constant scaling units.

# Attribution

Bonnet–Chang, proof of Theorem 2 in Section 6.
-/
theorem set_rounding_loss {n : ℕ} (w : Fin n → ℚ) (τ : ℚ)
    (nonnegative : ∀ v, 0 ≤ w v) (positive_scale : 0 < τ) (J : Finset (Fin n)) :
    weight w J - (J.card : ℚ) * τ ≤ τ * ((∑ v ∈ J, roundedCopies w τ v : ℕ) : ℚ) := by
  calc
    weight w J - (J.card : ℚ) * τ = ∑ v ∈ J, (w v - τ) := by
      simp [weight, Finset.sum_sub_distrib]
    _ ≤ ∑ v ∈ J, τ * (roundedCopies w τ v : ℚ) :=
      Finset.sum_le_sum fun v _ =>
        (Lax263307.RoundingBounds.pointwise_bounds w τ nonnegative positive_scale v).2
    _ = τ * ((∑ v ∈ J, roundedCopies w τ v : ℕ) : ℚ) := by
      push_cast
      rw [Finset.mul_sum]

/--
---
conclusion: Lax263307.RoundingBounds.total_copy_bound
---
The number of copies is at most `2n² / ε`.

# Proof strategy

Each floor is bounded by `w_v / τ`, and each weight by the maximum weight.
Sum these bounds and substitute the chosen scale.

# Attribution

Bonnet–Chang, proof of Theorem 2 in Section 6.
-/
theorem total_copy_bound {n : ℕ} (w : Fin n → ℚ) (ε : ℚ)
    (nonnegative : ∀ v, 0 ≤ w v) (positive_order : 0 < n)
    (positive_accuracy : 0 < ε) (positive_maximum : 0 < maximumWeight w) :
    ((∑ v, copies w ε v : ℕ) : ℚ) ≤ 2 * (n : ℚ) ^ 2 / ε := by
  have hτ := scale_positive w ε positive_order positive_accuracy positive_maximum
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt positive_order
  have hW : maximumWeight w ≠ 0 := ne_of_gt positive_maximum
  have hε : ε ≠ 0 := ne_of_gt positive_accuracy
  calc
    ((∑ v, copies w ε v : ℕ) : ℚ) = ∑ v, (copies w ε v : ℚ) := by norm_cast
    _ ≤ ∑ v, w v / scale w ε := Finset.sum_le_sum fun v _ =>
      Nat.floor_le (div_nonneg (nonnegative v) hτ.le)
    _ ≤ ∑ _v : Fin n, maximumWeight w / scale w ε :=
      Finset.sum_le_sum fun v _ => div_le_div_of_nonneg_right (le_maximum w v) hτ.le
    _ = (n : ℚ) * maximumWeight w / scale w ε := by simp; ring
    _ = 2 * (n : ℚ) ^ 2 / ε := by unfold scale; field_simp

end Lax263307Proofs.RoundingBounds
