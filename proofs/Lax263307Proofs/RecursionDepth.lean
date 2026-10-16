import Lax263307.RecursionDepth
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

namespace Lax263307Proofs.RecursionDepth

open Lax263307.RecursionDepth Lax263307.WeightedIndependentSet

theorem depth_mono : Monotone depth := by
  intro n m hnm
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
    by_cases hn : n ≤ 1
    · rw [depth, if_pos hn]
      exact Nat.zero_le _
    · have hm : ¬m ≤ 1 := by omega
      rw [depth.eq_def n, if_neg hn, depth.eq_def m, if_neg hm]
      exact Nat.add_le_add_left (ih (2 * m / 3) (by omega)
        (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hnm))) 1

/--
---
conclusion: Lax263307.RecursionDepth.balanced_decrease
---
Monotonicity of the integer depth function and its defining recurrence give
one fewer available level for every balanced child.
-/
theorem balanced_decrease (n m : ℕ) (nontrivial : 1 < n) (balanced : 3 * m ≤ 2 * n) :
    depth m + 1 ≤ depth n := by
  have hm : m ≤ 2 * n / 3 := by omega
  have hdepth := depth_mono hm
  rw [depth.eq_def n, if_neg (by omega)]
  omega

theorem depth_le_twice_exponent (L n : ℕ) (hn : n ≤ 2 ^ L) : depth n ≤ 2 * L := by
  induction L generalizing n with
  | zero =>
    have : n ≤ 1 := by simpa using hn
    simp [depth, this]
  | succ L ih =>
    by_cases hn₁ : n ≤ 1
    · simp [depth, hn₁]
    · rw [depth.eq_def n, if_neg hn₁]
      by_cases ha : 2 * n / 3 ≤ 1
      · rw [depth.eq_def (2 * n / 3), if_pos ha]
        omega
      · rw [depth.eq_def (2 * n / 3), if_neg ha]
        have hb : 2 * (2 * n / 3) / 3 ≤ 2 ^ L := by
          rw [pow_succ] at hn
          omega
        have := ih _ hb
        omega

/--
---
conclusion: Lax263307.RecursionDepth.logarithmic_bound
---
Two consecutive balanced reductions shrink the order by at least a factor
of two. Induction on the binary-power bound then gives the stated logarithmic
depth, also covering order zero.
-/
theorem logarithmic_bound (n : ℕ) : depth n ≤ 2 * (Nat.log2 n + 1) := by
  apply depth_le_twice_exponent
  rw [Nat.log2_eq_log_two]
  exact (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le

/--
---
conclusion: Lax263307.RecursionDepth.approximation_transfer
---
Bernoulli's inequality gives `(1-δ)^levels ≥ 1-levels*δ ≥ 1-ε`.
The certified upper bound dominates every independent-set cardinality,
so the returned set has the requested unweighted approximation guarantee.
-/
theorem approximation_transfer {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Finset (Fin n)) (u levels : ℕ) (δ ε : ℚ)
    (independent : G.IsIndepSet (I : Set (Fin n)))
    (upper_bound : ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card ≤ u)
    (_δ_nonnegative : 0 ≤ δ) (δ_small : δ ≤ 1)
    (ε_small : ε ≤ 1) (loss : (levels : ℚ) * δ ≤ ε)
    (size : (1 - δ) ^ levels * (u : ℚ) ≤ I.card) :
    IsApproximation G (fun _ => 1) ε I := by
  refine ⟨independent, ?_⟩
  intro J hJ
  have hbernoulli : 1 - (levels : ℚ) * δ ≤ (1 - δ) ^ levels := by
    simpa only [mul_neg, sub_eq_add_neg] using
      one_add_mul_le_pow (show (-2 : ℚ) ≤ -δ by linarith) levels
  have hfactor : 1 - ε ≤ (1 - δ) ^ levels := by linarith
  have hu : (J.card : ℚ) ≤ u := by exact_mod_cast upper_bound J hJ
  have hunonneg : (0 : ℚ) ≤ u := by positivity
  simp only [weight, Finset.sum_const, nsmul_eq_mul, mul_one]
  calc
    (1 - ε) * (J.card : ℚ) ≤ (1 - ε) * u := mul_le_mul_of_nonneg_left hu (by linarith)
    _ ≤ (1 - δ) ^ levels * u := mul_le_mul_of_nonneg_right hfactor hunonneg
    _ ≤ I.card := size

end Lax263307Proofs.RecursionDepth
