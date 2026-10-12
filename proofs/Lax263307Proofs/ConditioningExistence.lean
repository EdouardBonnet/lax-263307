import Lax263307.ConditioningExistence
import Lax263307Proofs.EntropyAlgebra
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.ConditioningExistence

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution Lax263307.Entropy
open EntropyAlgebra RelaxationAlgebra

theorem marginal_probability {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) (hy : IsFeasible G k r y)
    (A : Finset (Fin n)) (hA : A.card ≤ r) (hpos : 0 < value y A) (hk : 0 < k) :
    IsProbability (marginal y A k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := Lax263307.ConditionedCosts.conditioning_invariants G k r y hy A hA hpos
  refine ⟨fun v => div_nonneg (h.1 v).1 hkR.le, ?_⟩
  simp_rw [marginal, ← Finset.sum_div]
  rw [h.2.1, div_self (ne_of_gt hkR)]

/--
---
conclusion: Lax263307.ConditioningExistence.exists_low_edge_cost
---
The conditioning process reaches the required edge-cost threshold within
the available number of vertices.

# Proof strategy

Assume that every admissible small conditioning set exceeds the threshold.
Starting at the empty set, repeatedly apply the strict entropy-decrease
statement. After `r` steps the entropy would be strictly less than zero,
contradicting the entropy bounds. The resulting set inherits the checked
cost bounds and mass equation.

# Attribution

Bonnet–Chang, proof of Lemma 12.
-/
theorem exists_low_edge_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (target_positive : 0 < k) (level_positive : 0 < r) (threshold_positive : 0 < p)
    (budget : 2 * (p : ℝ) * Real.logb 2 n ≤ r) :
    ∃ A : Finset (Fin n), A.card ≤ r ∧ 0 < value y A ∧
      (∀ v, 0 ≤ conditioned y A v ∧ conditioned y A v ≤ 1) ∧
      (∑ v, conditioned y A v) = k ∧
      edgeCost G (conditioned y A) ≤ (k : ℝ) ^ 2 / p := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast threshold_positive
  have hzero : 0 < value y (∅ : Finset (Fin n)) := by rw [feasible.normalized]; norm_num
  have hprob0 := marginal_probability G k r y feasible ∅ (by simp) hzero target_positive
  have hbounds0 := Lax263307.EntropyBounds.entropy_bounds _ hprob0
  suffices hgood : ∃ A : Finset (Fin n), A.card ≤ r ∧ 0 < value y A ∧
      edgeCost G (conditioned y A) ≤ (k : ℝ) ^ 2 / p by
    obtain ⟨A, hA, hpos, he⟩ := hgood
    have h := Lax263307.ConditionedCosts.conditioning_invariants G k r y feasible A hA hpos
    exact ⟨A, hA, hpos, h.1, h.2.1, he⟩
  by_contra hnone
  push Not at hnone
  have hstep : ∀ t : ℕ, t ≤ r → ∃ A : Finset (Fin n), A.card ≤ t ∧ 0 < value y A ∧
      entropy (marginal y A k) ≤ entropy (marginal y ∅ k) - (t : ℝ) * (2 / p) ∧
      (0 < t → entropy (marginal y A k) < entropy (marginal y ∅ k) - (t : ℝ) * (2 / p)) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨∅, by simp, hzero, by simp, by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨A, hA, hpos, hH, _⟩ := ih (by omega)
      obtain ⟨v, hv, hdrop⟩ := Lax263307.EntropyDecrease.exists_entropy_decrease
        G k r p y feasible A (by omega) hpos target_positive threshold_positive
          (hnone A (by omega) hpos)
      have hkR : (0 : ℝ) < k := by exact_mod_cast target_positive
      have hcost : 0 < conditioned y A v := (div_pos_iff_of_pos_right hkR).1 hv
      have hnext := (Lax263307.ConditionedCosts.conditioning_invariants
        G k r y feasible A (by omega) hpos).2.2.2 v hcost
      have hcard : (insert v A).card ≤ t + 1 := by
        have := Finset.card_insert_le v A
        omega
      have hstrict : entropy (marginal y (insert v A) k) <
          entropy (marginal y ∅ k) - ((t + 1 : ℕ) : ℝ) * (2 / p) := by
        push_cast
        linarith
      exact ⟨insert v A, hcard, hnext, hstrict.le, fun _ => hstrict⟩
  obtain ⟨A, hA, hpos, _, hstrict⟩ := hstep r le_rfl
  have hbounds := Lax263307.EntropyBounds.entropy_bounds _
    (marginal_probability G k r y feasible A hA hpos target_positive)
  have hr : (0 : ℝ) < r := by exact_mod_cast level_positive
  have hlog : Real.logb 2 n ≤ (r : ℝ) / (2 * p) :=
    (le_div_iff₀ (mul_pos (by norm_num) hp)).2 (by nlinarith [budget])
  have hresource : (r : ℝ) / (2 * p) < (r : ℝ) * (2 / p) := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hp)).2
    field_simp
    nlinarith
  have hfinal := hstrict level_positive
  linarith

end Lax263307Proofs.ConditioningExistence
