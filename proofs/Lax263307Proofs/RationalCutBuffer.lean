import Lax263307.RationalCutBuffer
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

namespace Lax263307Proofs.RationalCutBuffer

open Matrix Lax263307.RationalCutBuffer

/--
---
conclusion: Lax263307.RationalCutBuffer.denominator_positive
---
-/
theorem denominator_positive {n : ℕ} (a : Fin n → ℚ) : 0 < denominator a := by
  exact Finset.prod_pos (fun i _ => (a i).den_pos)

/--
---
conclusion: Lax263307.RationalCutBuffer.integer_normal_cast
---
-/
theorem integer_normal_cast {n : ℕ} (a : Fin n → ℚ) (i : Fin n) :
    (integerNormal a i : ℝ) = (denominator a : ℝ) * (a i : ℝ) := by
  have hdvd : (a i).den ∣ denominator a :=
    Finset.dvd_prod_of_mem (fun i => (a i).den) (Finset.mem_univ i)
  have hdiv : (denominator a : ℚ) =
      (denominator a / (a i).den : ℕ) * ((a i).den : ℚ) := by
    exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  have h : (integerNormal a i : ℚ) = (denominator a : ℚ) * a i := by
    rw [integerNormal, Int.cast_mul, Int.cast_natCast]
    conv_rhs => rw [← (a i).num_div_den, hdiv]
    have hd : ((a i).den : ℚ) ≠ 0 := by exact_mod_cast (a i).den_ne_zero
    field_simp
  exact_mod_cast h

/--
---
conclusion: Lax263307.RationalCutBuffer.normal_nonzero
---
-/
theorem normal_nonzero {n : ℕ} (a : Fin n → ℚ) (x z : Fin n → ℝ)
    (gap : (fun i => (a i : ℝ)) ⬝ᵥ z < (fun i => (a i : ℝ)) ⬝ᵥ x) :
    ∃ i, integerNormal a i ≠ 0 := by
  by_contra! hzero
  have hD : (0 : ℝ) < denominator a := by exact_mod_cast denominator_positive a
  have ha (i : Fin n) : (a i : ℝ) = 0 := by
    have h := integer_normal_cast a i
    rw [hzero i, Int.cast_zero] at h
    nlinarith
  simp only [dotProduct, ha, zero_mul, Finset.sum_const_zero] at gap
  exact lt_irrefl _ gap

/--
---
conclusion: Lax263307.RationalCutBuffer.denominator_bound
---
-/
theorem denominator_bound {n : ℕ} (a : Fin n → ℚ) :
    denominator a ≤ 2 ^ (∑ i, Nat.size (a i).den) := by
  classical
  have h (s : Finset (Fin n)) :
      (∏ i ∈ s, (a i).den) ≤ 2 ^ (∑ i ∈ s, Nat.size (a i).den) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
      exact Nat.mul_le_mul (Nat.lt_size_self (a i).den).le ih
  exact h Finset.univ

/--
---
conclusion: Lax263307.RationalCutBuffer.normal_size
---
-/
theorem normal_size {n : ℕ} (a : Fin n → ℚ) (i : Fin n) :
    Nat.size (integerNormal a i).natAbs ≤
      Nat.size (a i).num.natAbs + ∑ j, Nat.size (a j).den := by
  have hclear : (integerNormal a i).natAbs ≤ (a i).num.natAbs * denominator a := by
    simp only [integerNormal, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (hclear.trans (Nat.mul_le_mul_left _ (denominator_bound a))).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity))

/--
---
conclusion: Lax263307.RationalCutBuffer.dot_stable
---
-/
theorem dot_stable {n : ℕ} (a x y : Fin n → ℝ) (ρ L : ℝ)
    (nonnegative : 0 ≤ ρ) (norm : (∑ i, |a i|) ≤ L)
    (near : ∀ i, |x i - y i| ≤ ρ) : |a ⬝ᵥ x - a ⬝ᵥ y| ≤ L * ρ := by
  unfold dotProduct
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |a i * x i - a i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * ρ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (near i) (abs_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right norm nonnegative

/--
---
conclusion: Lax263307.RationalCutBuffer.central_buffer
---
-/
theorem central_buffer {n : ℕ} (a x z perturbed : Fin n → ℝ) (α Δ ρ L : ℝ)
    (nonnegative : 0 ≤ ρ) (norm : (∑ i, |a i|) ≤ L)
    (valid : a ⬝ᵥ z ≤ α) (gap : α + Δ ≤ a ⬝ᵥ x)
    (small : L * ρ ≤ Δ / 2) (near : ∀ i, |perturbed i - z i| ≤ ρ) :
    a ⬝ᵥ perturbed ≤ a ⬝ᵥ x - Δ / 2 := by
  have h := (abs_le.mp (dot_stable a perturbed z ρ L nonnegative norm near)).2
  linarith

/--
---
conclusion: Lax263307.RationalCutBuffer.scaled_cleared_cut
---
-/
theorem scaled_cleared_cut {n : ℕ} (positive : 0 < n) (a : Fin n → ℚ)
    (query z : Fin n → ℝ) (α Δ ρ L : ℝ)
    (nonnegative : 0 ≤ ρ) (norm : (∑ i, |(a i : ℝ)|) ≤ L)
    (valid : (fun i => (a i : ℝ)) ⬝ᵥ z ≤ α)
    (gap : α + Δ ≤ (fun i => (a i : ℝ)) ⬝ᵥ (fun i => 4 * (n : ℝ) * query i))
    (small : L * ρ ≤ Δ / 2) (e : Fin n → ℝ)
    (near : ∀ i, |e i| ≤ ρ / (4 * n)) :
    (fun i => (integerNormal a i : ℝ)) ⬝ᵥ
      (Lax263307.BufferedEllipsoid.scale z + e - query) ≤ 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast positive
  let perturbed (i : Fin n) := 4 * (n : ℝ) * (Lax263307.BufferedEllipsoid.scale z i + e i)
  have hnear (i : Fin n) : |perturbed i - z i| ≤ ρ := by
    have heq : perturbed i - z i = 4 * (n : ℝ) * e i := by
      dsimp [perturbed, Lax263307.BufferedEllipsoid.scale]
      field_simp
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 4 * (n : ℝ))]
    have h := mul_le_mul_of_nonneg_left (near i) (by positivity : 0 ≤ 4 * (n : ℝ))
    have hc : 4 * (n : ℝ) * (ρ / (4 * n)) = ρ := by field_simp
    exact h.trans_eq hc
  have hcut := central_buffer (fun i => (a i : ℝ))
    (fun i => 4 * (n : ℝ) * query i) z perturbed α Δ ρ L nonnegative norm valid gap small hnear
  have hΔ : 0 ≤ Δ := by
    have hL : 0 ≤ L := (Finset.sum_nonneg (fun i _ => abs_nonneg (a i : ℝ))).trans norm
    nlinarith [mul_nonneg hL nonnegative]
  have hc : (fun i => (a i : ℝ)) ⬝ᵥ
      (Lax263307.BufferedEllipsoid.scale z + e - query) ≤ 0 := by
    have heq : (fun i => (a i : ℝ)) ⬝ᵥ perturbed -
        (fun i => (a i : ℝ)) ⬝ᵥ (fun i => 4 * (n : ℝ) * query i) =
        4 * (n : ℝ) * ((fun i => (a i : ℝ)) ⬝ᵥ
          (Lax263307.BufferedEllipsoid.scale z + e - query)) := by
      simp only [dotProduct, perturbed, Pi.add_apply, Pi.sub_apply]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h : 4 * (n : ℝ) * ((fun i => (a i : ℝ)) ⬝ᵥ
        (Lax263307.BufferedEllipsoid.scale z + e - query)) ≤ 0 := by
      rw [← heq]
      linarith
    exact nonpos_of_mul_nonpos_right h (by positivity)
  have hD : (0 : ℝ) ≤ denominator a := Nat.cast_nonneg _
  simp_rw [integer_normal_cast]
  unfold dotProduct at hc ⊢
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  exact mul_nonpos_of_nonneg_of_nonpos hD hc

end Lax263307Proofs.RationalCutBuffer
