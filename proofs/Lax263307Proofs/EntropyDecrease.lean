import Lax263307.EntropyDecrease
import Lax263307Proofs.EntropyAlgebra

namespace Lax263307Proofs.EntropyDecrease

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution
open Lax263307.Entropy EntropyAlgebra

theorem adjacencyMass_div {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℝ) (k : ℝ) (hk : k ≠ 0) :
    adjacencyMass G (fun v => x v / k) = adjacencyMass G x / k ^ 2 := by
  unfold adjacencyMass
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs
  · field_simp
  · simp

theorem positive_weight_decrease {n : ℕ} (π f : Fin n → ℝ) (hπ : IsProbability π)
    (H δ : ℝ) (havg : (∑ v, π v * f v) < H - δ) :
    ∃ v : Fin n, 0 < π v ∧ f v < H - δ := by
  have hconst : (∑ v, π v * (H - δ)) = H - δ := by
    rw [← Finset.sum_mul, hπ.2, one_mul]
  rw [← hconst] at havg
  obtain ⟨v, _, hv⟩ := Finset.exists_lt_of_sum_lt havg
  have hpos : 0 < π v := by
    by_contra h
    have hzero : π v = 0 := le_antisymm (not_lt.mp h) (hπ.1 v)
    simp [hzero] at hv
  exact ⟨v, hpos, (mul_lt_mul_iff_right₀ hpos).mp hv⟩

/--
---
conclusion: Lax263307.EntropyDecrease.exists_entropy_decrease
---
Exceeding the edge-cost threshold forces a positive-cost vertex whose
conditioning decreases entropy by more than the prescribed amount.

# Proof strategy

Normalize the costs by the target size and apply the average entropy-gap
inequality to the joint distribution. A strictly small weighted average
has a strictly small term with positive weight. The checked conditional
probability identities identify that term with the next conditioning step.

# Attribution

Bonnet–Chang, proof of Lemma 12, equation (18).
-/
theorem exists_entropy_decrease {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A : Finset (Fin n)) (size : A.card < r) (positive : 0 < value y A)
    (target_positive : 0 < k) (threshold_positive : 0 < p)
    (expensive : (k : ℝ) ^ 2 / p < edgeCost G (conditioned y A)) :
    ∃ v : Fin n, 0 < marginal y A k v ∧
      entropy (marginal y (insert v A) k) < entropy (marginal y A k) - 2 / p := by
  have hk : (0 : ℝ) < k := by exact_mod_cast target_positive
  have hp : (0 : ℝ) < p := by exact_mod_cast threshold_positive
  obtain ⟨hπ, hsum, hq, hsym, hmarg, hedge, hcond⟩ :=
    Lax263307.ConditioningDistribution.distribution_identities
      G k r y feasible A size positive target_positive
  have hprob : IsProbability (marginal y A k) := ⟨hπ, hsum⟩
  have hgap := Lax263307.EntropyGap.average_entropy_gap
    G (marginal y A k) (joint y A k) hprob hq hsym hmarg hedge
  have hscaled : adjacencyMass G (marginal y A k) =
      adjacencyMass G (conditioned y A) / (k : ℝ) ^ 2 :=
    adjacencyMass_div G (conditioned y A) k (ne_of_gt hk)
  have hmass : (2 : ℝ) / p < adjacencyMass G (marginal y A k) := by
    rw [hscaled]
    apply (div_lt_div_iff₀ hp (sq_pos_of_pos hk)).2
    have h := (div_lt_iff₀ hp).1 expensive
    unfold edgeCost at h
    nlinarith
  have havg : (∑ v, marginal y A k v * entropy (fun u => joint y A k u v / marginal y A k v)) <
      entropy (marginal y A k) - 2 / p := by linarith
  obtain ⟨v, hv, hdrop⟩ := positive_weight_decrease (marginal y A k)
    (fun v => entropy (fun u => joint y A k u v / marginal y A k v))
    hprob (entropy (marginal y A k)) (2 / p) havg
  refine ⟨v, hv, ?_⟩
  have heq : marginal y (insert v A) k =
      fun u => joint y A k u v / marginal y A k v := by
    funext u
    exact hcond u v hv
  rw [heq]
  exact hdrop

end Lax263307Proofs.EntropyDecrease
