import Lax263307.EntropyGap
import Lax263307Proofs.EntropyAlgebra

namespace Lax263307Proofs.EntropyGap

open Lax263307.Entropy EntropyAlgebra

theorem joint_entry_le {n : ℕ} (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (hq : ∀ u v, 0 ≤ q u v) (hm : ∀ v, (∑ u, q u v) = π v) (u v : Fin n) :
    q u v ≤ π v := by
  rw [← hm v]
  exact Finset.single_le_sum (fun i _ => hq i v) (Finset.mem_univ u)

theorem row_marginal {n : ℕ} (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (hs : ∀ u v, q u v = q v u) (hm : ∀ v, (∑ u, q u v) = π v) (u : Fin n) :
    (∑ v, q u v) = π u := by
  simp_rw [hs u]
  exact hm u

theorem weighted_conditional_entropy {n : ℕ} (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (hπ : IsProbability π) (hq : ∀ u v, 0 ≤ q u v)
    (hm : ∀ v, (∑ u, q u v) = π v) :
    (∑ v, π v * naturalEntropy (fun u => q u v / π v)) =
      (∑ v, ∑ u, Real.negMulLog (q u v)) - naturalEntropy π := by
  have hpoint (u v : Fin n) :
      π v * Real.negMulLog (q u v / π v) =
        Real.negMulLog (q u v) + q u v * Real.log (π v) := by
    rcases eq_or_lt_of_le (hπ.1 v) with hv | hv
    · have hzero : q u v = 0 := le_antisymm
        ((joint_entry_le π q hq hm u v).trans_eq hv.symm) (hq u v)
      simp [← hv, hzero]
    · exact scaled_negMulLog_div _ _ hv
  simp_rw [naturalEntropy, Finset.mul_sum, hpoint, Finset.sum_add_distrib,
    ← Finset.sum_mul, hm]
  simp [Real.negMulLog, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem natural_gap_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (hπ : IsProbability π) (hq : ∀ u v, 0 ≤ q u v)
    (hs : ∀ u v, q u v = q v u) (hm : ∀ v, (∑ u, q u v) = π v)
    (he : ∀ u v, G.Adj u v → q u v = 0) :
    adjacencyMass G π ≤ naturalEntropy π -
      ∑ v, π v * naturalEntropy (fun u => q u v / π v) := by
  let cost := fun u v => -Real.negMulLog (q u v) -
    q u v * Real.log (π u) - q u v * Real.log (π v)
  have hpoint (u v : Fin n) :
      q u v - π u * π v + (if G.Adj u v then π u * π v else 0) ≤ cost u v := by
    by_cases hedge : G.Adj u v
    · simp [cost, hedge, he u v hedge]
    · simp only [if_neg hedge, add_zero]
      rcases eq_or_lt_of_le (hq u v) with hzero | hpos
      · simp only [← hzero, Real.negMulLog_zero, zero_mul, sub_zero, zero_sub, cost]
        simpa using neg_nonpos.mpr (mul_nonneg (hπ.1 u) (hπ.1 v))
      · have hv := lt_of_lt_of_le hpos (joint_entry_le π q hq hm u v)
        have hu := lt_of_lt_of_le (hpos.trans_eq (hs u v)) (joint_entry_le π q hq hm v u)
        exact relative_term_bound _ _ _ hpos hu hv
  have htotal : (∑ v, ∑ u, q u v) = 1 := by simp_rw [hm]; exact hπ.2
  have hproduct : (∑ v, ∑ u, π u * π v) = 1 := by
    simp_rw [← Finset.sum_mul, hπ.2, one_mul]
    exact hπ.2
  have hcrossV : (∑ v, ∑ u, q u v * Real.log (π v)) = -naturalEntropy π := by
    simp only [← Finset.sum_mul, hm, naturalEntropy, Real.negMulLog,
      neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hcrossU : (∑ v, ∑ u, q u v * Real.log (π u)) = -naturalEntropy π := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, row_marginal π q hs hm, naturalEntropy,
      Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun v _ =>
    Finset.sum_le_sum (s := Finset.univ) fun u _ => hpoint u v
  have hadj : (∑ v, ∑ u, if G.Adj u v then π u * π v else 0) = adjacencyMass G π := by
    rw [Finset.sum_comm]
    rfl
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, cost,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsum
  rw [htotal, hproduct, hadj, hcrossU, hcrossV] at hsum
  rw [weighted_conditional_entropy π q hπ hq hm]
  linarith

/--
---
conclusion: Lax263307.EntropyGap.average_entropy_gap
---
The expected entropy decrease is at least the product probability of
ordered adjacent pairs.

# Proof strategy

The entropy chain rule expresses the decrease as a relative-entropy sum.
The inequality `log x ≤ x - 1` bounds each positive-support term below
by joint mass minus product mass. Edge pairs have zero joint mass, so
their product mass contributes to the gap. Zero marginals are treated
explicitly. Divide by `log 2` to obtain the inequality in bits.

# Attribution

Bonnet–Chang, proof of Lemma 12, equations (17) and (18).
-/
theorem average_entropy_gap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (π : Fin n → ℝ) (q : Fin n → Fin n → ℝ)
    (probability : IsProbability π) (nonnegative : ∀ u v, 0 ≤ q u v)
    (symmetric : ∀ u v, q u v = q v u)
    (marginals : ∀ v, (∑ u, q u v) = π v)
    (edge_zero : ∀ u v, G.Adj u v → q u v = 0) :
    adjacencyMass G π ≤ entropy π - ∑ v, π v * entropy (fun u => q u v / π v) := by
  have hgap := natural_gap_bound G π q probability nonnegative symmetric marginals edge_zero
  have hmass : 0 ≤ adjacencyMass G π := by
    apply Finset.sum_nonneg
    intro u _
    apply Finset.sum_nonneg
    intro v _
    split_ifs
    · exact mul_nonneg (probability.1 u) (probability.1 v)
    · exact le_rfl
  have hm : adjacencyMass G π * Real.log 2 ≤ adjacencyMass G π := by
    nlinarith [log_two_le_one]
  simp_rw [entropy, ← mul_div_assoc, ← Finset.sum_div, ← sub_div]
  exact (le_div_iff₀ log_two_pos).2 (hm.trans hgap)

end Lax263307Proofs.EntropyGap
