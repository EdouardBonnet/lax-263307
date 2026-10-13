import Lax263307.BufferedEllipsoid
import Mathlib.Tactic

namespace Lax263307Proofs.BufferedEllipsoid

open Matrix Lax263307.BufferedEllipsoid

/--
---
conclusion: Lax263307.BufferedEllipsoid.coordinate_ball_bound
---
A single coordinate square is bounded by the sum of squares; take the nonnegative square root bound.
-/
theorem coordinate_ball_bound {n : ℕ} (e : Fin n → ℝ) (ρ : ℝ) (nonnegative : 0 ≤ ρ)
    (ball : e ⬝ᵥ e ≤ ρ ^ 2) : ∀ i, |e i| ≤ ρ := by
  intro i
  have h : (e i) ^ 2 ≤ ∑ j, (e j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (e j)) (Finset.mem_univ i)
  have hs : (e i) ^ 2 ≤ ρ ^ 2 := h.trans (by simpa only [dotProduct, pow_two] using ball)
  simpa only [abs_of_nonneg nonnegative] using (sq_le_sq).mp hs

/--
---
conclusion: Lax263307.BufferedEllipsoid.scaled_cube_norm
---
Each scaled coordinate lies between zero and 1/(4n). Sum the squared bounds and use n≥1.
-/
theorem scaled_cube_norm {n : ℕ} (positive : 0 < n) (z : Fin n → ℝ)
    (cube : ∀ i, 0 ≤ z i ∧ z i ≤ 1) : scale z ⬝ᵥ scale z ≤ (1 / 16 : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast positive
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast positive
  have each (i : Fin n) : (scale z i) ^ 2 ≤ (1 / (4 * (n : ℝ))) ^ 2 := by
    have hlow : 0 ≤ scale z i := div_nonneg (cube i).1 (by positivity)
    have hhigh : scale z i ≤ 1 / (4 * (n : ℝ)) := div_le_div_of_nonneg_right (cube i).2 (by positivity)
    exact pow_le_pow_left₀ hlow hhigh 2
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => each i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have heq : (n : ℝ) * (1 / (4 * (n : ℝ))) ^ 2 = 1 / (16 * n) := by field_simp; ring
  have hbound : 1 / (16 * (n : ℝ)) ≤ (1 / 16 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  simpa only [dotProduct, pow_two] using hsum.trans (heq.le.trans hbound)

/--
---
conclusion: Lax263307.BufferedEllipsoid.initial_ball
---
The squared norm of a sum is at most twice each summand square. Both the scaled cube point and the perturbation have squared norm at most 1/16.
-/
theorem initial_ball {n : ℕ} (positive : 0 < n) (z : Fin n → ℝ)
    (cube : ∀ i, 0 ≤ z i ∧ z i ≤ 1) (ρ : ℝ) (nonnegative : 0 ≤ ρ) (small : ρ ≤ 1 / 4)
    (e : Fin n → ℝ) (ball : e ⬝ᵥ e ≤ ρ ^ 2) :
    (scale z + e) ⬝ᵥ (scale z + e) ≤ 1 := by
  have hscale := scaled_cube_norm positive z cube
  have hr : ρ ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    show (scale z i + e i) ^ 2 ≤ 2 * (scale z i) ^ 2 + 2 * (e i) ^ 2 from by
      nlinarith [sq_nonneg (scale z i - e i)])
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hs' : (scale z + e) ⬝ᵥ (scale z + e) ≤ 2 * (scale z ⬝ᵥ scale z) + 2 * (e ⬝ᵥ e) := by
    simpa only [dotProduct, pow_two, Pi.add_apply] using hs
  linarith

/--
---
conclusion: Lax263307.BufferedEllipsoid.integer_normal_norm
---
A nonzero integer coordinate has squared magnitude at least one. Its square is bounded by the sum of all coordinate squares.
-/
theorem integer_normal_norm {n : ℕ} (a : Fin n → ℤ) (nonzero : ∃ i, a i ≠ 0) :
    1 ≤ (fun i => (a i : ℝ)) ⬝ᵥ (fun i => (a i : ℝ)) := by
  obtain ⟨i, hi⟩ := nonzero
  have hs : (0 : ℤ) < (a i) ^ 2 := sq_pos_of_ne_zero hi
  have hsi : (1 : ℤ) ≤ (a i) ^ 2 := by omega
  have hsr : (1 : ℝ) ≤ (a i : ℝ) ^ 2 := by exact_mod_cast hsi
  have hsum := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    sq_nonneg (a j : ℝ)) (Finset.mem_univ i)
  exact hsr.trans (by simpa only [dotProduct, pow_two] using hsum)




end Lax263307Proofs.BufferedEllipsoid
