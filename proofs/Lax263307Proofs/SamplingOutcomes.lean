import Lax263307.SamplingOutcomes
import Mathlib.Tactic

namespace Lax263307Proofs.SamplingOutcomes

open Lax263307.PathSampling Lax263307.SamplingOutcomes

theorem event_union_bound {n q : ℕ} (P : Distribution n q) (A B : Set (Fin q)) :
    eventProbability P (A ∪ B) ≤ eventProbability P A + eventProbability P B := by
  classical
  unfold eventProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [ha, hb, P.nonnegative i]

theorem event_complement {n q : ℕ} (P : Distribution n q) (A : Set (Fin q)) :
    eventProbability P Aᶜ = 1 - eventProbability P A := by
  classical
  have heq : eventProbability P Aᶜ + eventProbability P A = 1 := by
    unfold eventProbability
    rw [← Finset.sum_add_distrib, ← P.normalized]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ A <;> simp [hi]
  linarith

/--
---
conclusion: Lax263307.SamplingOutcomes.markov_bound
---
On the event that cost exceeds the threshold, multiply that threshold by the
outcome probability and bound it by the weighted cost. Nonnegative cost
controls the other outcomes. Sum and divide by the positive threshold.
-/
theorem markov_bound {n q : ℕ} (P : Distribution n q) (cost : Fin q → ℝ)
    (nonnegative : ∀ i, 0 ≤ cost i) (T : ℝ) (positive : 0 < T) :
    eventProbability P {i | T < cost i} ≤ (∑ i, P.probability i * cost i) / T := by
  classical
  apply (le_div_iff₀ positive).mpr
  unfold eventProbability
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  change (if T < cost i then P.probability i else 0) * T ≤ P.probability i * cost i
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h.le (P.nonnegative i)
  · simpa using mul_nonneg (P.nonnegative i) (nonnegative i)

/--
---
conclusion: Lax263307.SamplingOutcomes.good_outcome
---
Markov bounds the probability of cost exceeding `4M` by one quarter. Union
with the bad event has probability at most one half, so its complement has
positive probability. A positive summand supplies the desired outcome.

# Attribution

Bonnet–Chang, choice of the sampled routes in Lemma 11.
-/
theorem good_outcome {n q : ℕ} (P : Distribution n q) (bad : Set (Fin q))
    (cost : Fin q → ℝ) (M : ℝ) (positive : 0 < M)
    (nonnegative : ∀ i, 0 ≤ cost i)
    (bad_bound : eventProbability P bad ≤ 1 / 4)
    (expected_bound : (∑ i, P.probability i * cost i) ≤ M) :
    ∃ i, 0 < P.probability i ∧ i ∉ bad ∧ cost i ≤ 4 * M := by
  classical
  let expensive : Set (Fin q) := {i | 4 * M < cost i}
  have hcost : eventProbability P expensive ≤ 1 / 4 := by
    calc
      eventProbability P expensive ≤ (∑ i, P.probability i * cost i) / (4 * M) :=
        Lax263307.SamplingOutcomes.markov_bound P cost nonnegative (4 * M) (by positivity)
      _ ≤ M / (4 * M) := div_le_div_of_nonneg_right expected_bound (by positivity)
      _ = 1 / 4 := by field_simp
  have hbad : eventProbability P (bad ∪ expensive) ≤ 1 / 2 := by
    have hu := event_union_bound P bad expensive
    linarith
  have hgood : 0 < eventProbability P (bad ∪ expensive)ᶜ := by
    rw [event_complement]
    linarith
  unfold eventProbability at hgood
  obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt
    (show (∑ _i : Fin q, (0 : ℝ)) <
      ∑ i, if i ∈ (bad ∪ expensive)ᶜ then P.probability i else 0 from by simpa using hgood)
  by_cases hmem : i ∈ (bad ∪ expensive)ᶜ
  · rw [if_pos hmem] at hi
    have hnb : i ∉ bad := fun hb => hmem (Or.inl hb)
    have hnc : cost i ≤ 4 * M := le_of_not_gt (fun hc => hmem (Or.inr hc))
    exact ⟨i, hi, hnb, hnc⟩
  · simp only [if_neg hmem, lt_self_iff_false] at hi

end Lax263307Proofs.SamplingOutcomes
