import Lax263307.HeavyConditioning
import Lax263307Proofs.EntropyDecrease
import Lax263307Proofs.ConditioningExistence
import Lax263307Proofs.LightSeparators
import Mathlib.Tactic

namespace Lax263307Proofs.HeavyConditioning

open Lax263307.Entropy Lax263307.HeavyConditioning

theorem heavy_weight_decrease {n : ℕ} (π f : Fin n → ℝ) (probability : IsProbability π)
    (nonnegative : ∀ v, 0 < π v → 0 ≤ f v) (H L p : ℝ)
    (hH : 0 ≤ H) (hHL : H ≤ L) (hL : 0 < L) (hp : 0 < p) (hn : 0 < n)
    (average : (∑ v, π v * f v) < H - 2 / p) :
    ∃ v : Fin n, 1 / (2 * (n : ℝ) * p * L) ≤ π v ∧ f v < H - 1 / p := by
  classical
  let τ : ℝ := 1 / (2 * (n : ℝ) * p * L)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hτ : 0 < τ := by dsimp [τ]; positivity
  by_contra hnone
  push Not at hnone
  have each (v : Fin n) : π v * (H - f v) ≤ π v / p + τ * L := by
    by_cases hv : τ ≤ π v
    · have hfv := hnone v hv
      have hprod := mul_le_mul_of_nonneg_left (show H - f v ≤ 1 / p by linarith) (probability.1 v)
      have hτL : 0 ≤ τ * L := mul_nonneg hτ.le hL.le
      simpa only [mul_one_div] using hprod.trans (le_add_of_nonneg_right hτL)
    · have hsmall : π v ≤ τ := (not_le.mp hv).le
      have hprod : π v * (H - f v) ≤ π v * H := by
        by_cases hpos : 0 < π v
        · exact mul_le_mul_of_nonneg_left (by linarith [nonnegative v hpos]) (probability.1 v)
        · have hz : π v = 0 := le_antisymm (not_lt.mp hpos) (probability.1 v)
          simp [hz]
      have hmul : π v * H ≤ τ * L :=
        (mul_le_mul_of_nonneg_right hsmall hH).trans (mul_le_mul_of_nonneg_left hHL hτ.le)
      exact (hprod.trans hmul).trans (le_add_of_nonneg_left (div_nonneg (probability.1 v) hp.le))
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin n))) => each v)
  simp only [Finset.sum_sub_distrib, mul_sub, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Finset.sum_div, probability.2, one_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hτeq : (n : ℝ) * τ * L = 1 / (2 * p) := by
    dsimp [τ]
    field_simp
  rw [hτeq] at hsum
  have hfrac : 1 / p + 1 / (2 * p) < 2 / p := by
    field_simp
    nlinarith
  linarith


open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution
open Lax263307Proofs.EntropyDecrease Lax263307Proofs.ConditioningExistence


/--
---
conclusion: Lax263307.HeavyConditioning.heavy_entropy_decrease
---
The expected entropy drop exceeds 2/p. Choices below the probability
floor contribute at most 1/(2p), using the parent entropy bound. If every
remaining choice dropped by at most 1/p, the total drop would be at most
3/(2p), a contradiction. Conditional moment identities identify the
selected entropy with that of the enlarged conditioning set.
-/
theorem heavy_entropy_decrease {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A : Finset (Fin n)) (size : A.card < r) (positive : 0 < value y A)
    (target_positive : 0 < k) (threshold_positive : 0 < p) (order_positive : 0 < n)
    (expensive : (k : ℝ) ^ 2 / p < edgeCost G (conditioned y A)) :
    ∃ v : Fin n, probabilityFloor n p ≤ marginal y A k v ∧
      entropy (marginal y (insert v A) k) < entropy (marginal y A k) - 1 / p := by
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
  have hnonnegative (v : Fin n) (hv : 0 < marginal y A k v) :
      0 ≤ entropy (fun u => joint y A k u v / marginal y A k v) := by
    have hcost : 0 < conditioned y A v := (div_pos_iff_of_pos_right hk).mp hv
    have hnext := (Lax263307.ConditionedCosts.conditioning_invariants
      G k r y feasible A size.le positive).2.2.2 v hcost
    have hcard : (insert v A).card ≤ r := (Finset.card_insert_le v A).trans (by omega)
    have h := (Lax263307.EntropyBounds.entropy_bounds _
      (marginal_probability G k r y feasible (insert v A) hcard hnext target_positive)).1
    have heq : marginal y (insert v A) k = fun u => joint y A k u v / marginal y A k v :=
      funext (fun u => hcond u v hv)
    rwa [heq] at h
  have hb := Lax263307.EntropyBounds.entropy_bounds _ hprob
  have hL : Real.logb 2 n ≤ (Nat.log2 n : ℝ) + 1 :=
    Lax263307Proofs.LightSeparators.logFactor_upper n
  obtain ⟨v, hv, hdrop⟩ := heavy_weight_decrease (marginal y A k)
    (fun v => entropy (fun u => joint y A k u v / marginal y A k v)) hprob hnonnegative
    (entropy (marginal y A k)) ((Nat.log2 n : ℝ) + 1) p hb.1 (hb.2.trans hL)
    (by positivity) hp order_positive havg
  have hfloor : 0 < probabilityFloor n p := by unfold probabilityFloor; positivity
  have hvpos : 0 < marginal y A k v := hfloor.trans_le hv
  refine ⟨v, hv, ?_⟩
  have heq : marginal y (insert v A) k = fun u => joint y A k u v / marginal y A k v :=
    funext (fun u => hcond u v hvpos)
  rwa [heq]


/--
---
conclusion: Lax263307.HeavyConditioning.heavy_low_edge_cost
---
Induct through heavy entropy-decreasing choices, retaining raw moment
at least tau^t after t steps. The raw moment of each new set multiplies
by k times its marginal probability, hence by at least tau since k≥1.
If every admissible set above the final moment floor remained expensive,
r steps would force negative entropy. Conditioning invariants supply
the bounded costs and exact mass of the resulting sparse set.
-/
theorem heavy_low_edge_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : MomentVector n r) (feasible : IsFeasible G k r y)
    (order_positive : 0 < n) (target_positive : 0 < k)
    (level_positive : 0 < r) (threshold_positive : 0 < p)
    (budget : (p : ℝ) * ((Nat.log2 n : ℝ) + 1) ≤ r) :
    ∃ A : Finset (Fin n), A.card ≤ r ∧ probabilityFloor n p ^ r ≤ value y A ∧
      0 < value y A ∧ (∀ v, 0 ≤ conditioned y A v ∧ conditioned y A v ≤ 1) ∧
      (∑ v, conditioned y A v) = k ∧ edgeCost G (conditioned y A) ≤ (k : ℝ) ^ 2 / p := by
  classical
  have hn : (0 : ℝ) < n := by exact_mod_cast order_positive
  have hk : (0 : ℝ) < k := by exact_mod_cast target_positive
  have hp : (0 : ℝ) < p := by exact_mod_cast threshold_positive
  let τ := probabilityFloor n p
  have hτ : 0 < τ := by dsimp [τ, probabilityFloor]; positivity
  have hτ1 : τ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast order_positive
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast threshold_positive
    dsimp [τ, probabilityFloor]
    apply (div_le_one (by positivity)).mpr
    have hL : (1 : ℝ) ≤ (Nat.log2 n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    nlinarith [mul_le_mul hn1 hp1 (by positivity) (by norm_num)]
  have hzero : value y (∅ : Finset (Fin n)) = 1 := feasible.normalized
  have hprob0 := marginal_probability G k r y feasible ∅ (by simp) (by rw [hzero]; norm_num) target_positive
  have hbounds0 := Lax263307.EntropyBounds.entropy_bounds _ hprob0
  have hL : entropy (marginal y ∅ k) ≤ (Nat.log2 n : ℝ) + 1 :=
    hbounds0.2.trans (Lax263307Proofs.LightSeparators.logFactor_upper n)
  suffices hgood : ∃ A : Finset (Fin n), A.card ≤ r ∧ τ ^ r ≤ value y A ∧
      0 < value y A ∧ edgeCost G (conditioned y A) ≤ (k : ℝ) ^ 2 / p by
    obtain ⟨A, hA, hval, hpos, he⟩ := hgood
    have h := Lax263307.ConditionedCosts.conditioning_invariants G k r y feasible A hA hpos
    exact ⟨A, hA, hval, hpos, h.1, h.2.1, he⟩
  by_contra hnone
  push Not at hnone
  have hstep : ∀ t : ℕ, t ≤ r → ∃ A : Finset (Fin n), A.card ≤ t ∧ τ ^ t ≤ value y A ∧
      0 < value y A ∧ entropy (marginal y A k) ≤ entropy (marginal y ∅ k) - (t : ℝ) / p ∧
      (0 < t → entropy (marginal y A k) < entropy (marginal y ∅ k) - (t : ℝ) / p) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨∅, by simp, by simp [hzero], by rw [hzero]; norm_num, by simp, by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨A, hA, hval, hpos, hH, _⟩ := ih (by omega)
      have hvalr : τ ^ r ≤ value y A :=
        (pow_le_pow_of_le_one hτ.le hτ1 (by omega : t ≤ r)).trans hval
      obtain ⟨v, hv, hdrop⟩ := Lax263307.HeavyConditioning.heavy_entropy_decrease G k r p y feasible A (by omega) hpos
        target_positive threshold_positive order_positive (hnone A (by omega) hvalr hpos)
      have hvpos : 0 < marginal y A k v := hτ.trans_le hv
      have hcost : 0 < conditioned y A v := (div_pos_iff_of_pos_right hk).mp hvpos
      have hnext := (Lax263307.ConditionedCosts.conditioning_invariants
        G k r y feasible A (by omega) hpos).2.2.2 v hcost
      have heq : value y (insert v A) = (k : ℝ) * marginal y A k v * value y A := by
        unfold marginal conditioned
        field_simp
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast target_positive
      have hprod : τ * value y A ≤ value y (insert v A) := by
        rw [heq]
        have hkmarg : τ ≤ (k : ℝ) * marginal y A k v :=
          hv.trans (by nlinarith)
        exact mul_le_mul_of_nonneg_right hkmarg hpos.le
      have hnextval : τ ^ (t + 1) ≤ value y (insert v A) := by
        rw [pow_succ]
        exact (mul_le_mul_of_nonneg_right hval hτ.le).trans (by simpa [mul_comm] using hprod)
      have hcard : (insert v A).card ≤ t + 1 := (Finset.card_insert_le v A).trans (by omega)
      have hstrict : entropy (marginal y (insert v A) k) <
          entropy (marginal y ∅ k) - ((t + 1 : ℕ) : ℝ) / p := by
        push_cast
        rw [add_div]
        linarith
      exact ⟨insert v A, hcard, hnextval, hnext, hstrict.le, fun _ => hstrict⟩
  obtain ⟨A, hA, _hval, hpos, _hH, hstrict⟩ := hstep r le_rfl
  have hnonnegative := (Lax263307.EntropyBounds.entropy_bounds _
    (marginal_probability G k r y feasible A hA hpos target_positive)).1
  have hbudget : (Nat.log2 n : ℝ) + 1 ≤ (r : ℝ) / p := (le_div_iff₀ hp).mpr (by nlinarith [budget])
  have hfinal := hstrict level_positive
  linarith

end Lax263307Proofs.HeavyConditioning
