import Lax263307.PathSampling

/-!
---
title: Choosing a collision-free outcome with bounded total path length
type: theorem
---
For a finite probability distribution, suppose the probability of a bad
outcome is at most $1/4$ and a nonnegative total cost has expectation at most
$M>0$. Some outcome of positive probability is not bad and has total cost
at most $4M$. This combines the union bound with Markov's inequality.

# Attribution

Bonnet–Chang, the simultaneous choice of noninteracting routes and bounded
total path length in Lemma 11.
-/

namespace Lax263307.SamplingOutcomes

open PathSampling

/-- Probability of an event in the finite outcome space. -/
noncomputable def eventProbability {n q : ℕ} (P : Distribution n q)
    (event : Set (Fin q)) : ℝ := by
  classical
  exact ∑ i, if i ∈ event then P.probability i else 0

/-- Markov's inequality for a nonnegative cost and a positive threshold. -/
axiom markov_bound {n q : ℕ} (P : Distribution n q) (cost : Fin q → ℝ)
    (nonnegative : ∀ i, 0 ≤ cost i) (T : ℝ) (positive : 0 < T) :
    eventProbability P {i | T < cost i} ≤ (∑ i, P.probability i * cost i) / T

/-- One positive-probability outcome meets both requirements. -/
axiom good_outcome {n q : ℕ} (P : Distribution n q) (bad : Set (Fin q))
    (cost : Fin q → ℝ) (M : ℝ) (positive : 0 < M)
    (nonnegative : ∀ i, 0 ≤ cost i)
    (bad_bound : eventProbability P bad ≤ 1 / 4)
    (expected_bound : (∑ i, P.probability i * cost i) ≤ M) :
    ∃ i, 0 < P.probability i ∧ i ∉ bad ∧ cost i ≤ 4 * M

end Lax263307.SamplingOutcomes
