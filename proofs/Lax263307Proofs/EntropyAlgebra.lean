import Lax263307.Entropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

namespace Lax263307Proofs.EntropyAlgebra

open Lax263307.Entropy

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at this ⊢
  exact this

theorem probability_entry_le_one {n : ℕ} (π : Fin n → ℝ) (hπ : IsProbability π)
    (v : Fin n) : π v ≤ 1 := by
  rw [← hπ.2]
  exact Finset.single_le_sum (fun u _ => hπ.1 u) (Finset.mem_univ v)

theorem scaled_negMulLog_div (a x : ℝ) (ha : 0 < a) :
    a * Real.negMulLog (x / a) = Real.negMulLog x + x * Real.log a := by
  by_cases hx : x = 0
  · simp [hx]
  · dsimp [Real.negMulLog]
    rw [Real.log_div hx (ne_of_gt ha)]
    field_simp
    ring

theorem relative_term_bound (x a b : ℝ) (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) :
    x - a * b ≤ -Real.negMulLog x - x * Real.log a - x * Real.log b := by
  have hab : 0 < a * b := mul_pos ha hb
  have h := Real.log_le_sub_one_of_pos (div_pos hab hx)
  rw [Real.log_div (ne_of_gt hab) (ne_of_gt hx),
    Real.log_mul (ne_of_gt ha) (ne_of_gt hb)] at h
  have hm := mul_le_mul_of_nonneg_left h hx.le
  simp_rw [mul_sub] at hm
  rw [mul_div_cancel₀ _ (ne_of_gt hx), mul_one] at hm
  dsimp [Real.negMulLog]
  nlinarith

theorem natural_entropy_nonneg {n : ℕ} (π : Fin n → ℝ) (hπ : IsProbability π) :
    0 ≤ naturalEntropy π :=
  Finset.sum_nonneg fun v _ => Real.negMulLog_nonneg (hπ.1 v) (probability_entry_le_one π hπ v)

theorem natural_entropy_le_log {n : ℕ} (π : Fin n → ℝ) (hπ : IsProbability π) :
    naturalEntropy π ≤ Real.log n := by
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    simpa using hπ.2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hw : (∑ _v : Fin n, (1 / (n : ℝ))) = 1 := by simp [hn0]
  have h := Real.concaveOn_negMulLog.le_map_sum
    (t := Finset.univ) (w := fun _ : Fin n => 1 / (n : ℝ)) (p := π)
    (fun _ _ => (one_div_pos.mpr hnR).le) hw (fun v _ => hπ.1 v)
  simp only [smul_eq_mul] at h
  simp_rw [← Finset.mul_sum] at h
  rw [hπ.2, mul_one] at h
  have hm := mul_le_mul_of_nonneg_left h hnR.le
  rw [← mul_assoc, mul_one_div_cancel hn0, one_mul] at hm
  have heq : (n : ℝ) * Real.negMulLog (1 / (n : ℝ)) = Real.log n := by
    simp [Real.negMulLog, hn0]
  exact hm.trans_eq heq

end Lax263307Proofs.EntropyAlgebra
