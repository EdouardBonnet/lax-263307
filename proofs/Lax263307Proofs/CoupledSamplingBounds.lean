import Lax263307.CoupledSamplingBounds
import Mathlib.Tactic

namespace Lax263307Proofs.CoupledSamplingBounds

open Lax263307.RouteDistributions Lax263307.CoupledRouteSampling Lax263307.CoupledSamplingBounds

variable {Ω I J : Type*} [Fintype Ω] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem integrate_single (w : Ω → ℝ) (X : Ω → I) (p : I → ℝ)
    (law : ∀ i, (∑ ω, w ω * (if X ω = i then (1 : ℝ) else 0)) = p i)
    (h : I → ℝ) : (∑ ω, w ω * h (X ω)) = ∑ i, p i * h i := by
  classical
  have hterm (ω : Ω) : w ω * h (X ω) =
      ∑ i, w ω * (if X ω = i then (1 : ℝ) else 0) * h i := by
    simp [mul_ite, eq_comm]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, law]

theorem integrate_pair (w : Ω → ℝ) (X : Ω → I) (Y : Ω → J) (p : I → ℝ) (r : J → ℝ)
    (law : ∀ i j, (∑ ω, w ω * ((if X ω = i then (1 : ℝ) else 0) *
      (if Y ω = j then (1 : ℝ) else 0))) = p i * r j)
    (h : I → J → ℝ) :
    (∑ ω, w ω * h (X ω) (Y ω)) = ∑ i, ∑ j, (p i * r j) * h i j := by
  classical
  have hterm (ω : Ω) : w ω * h (X ω) (Y ω) =
      ∑ i, ∑ j, w ω * ((if X ω = i then (1 : ℝ) else 0) *
        (if Y ω = j then (1 : ℝ) else 0)) * h i j := by
    simp [mul_ite, eq_comm]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, law]

theorem single_edge_expectation {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t)
    (e : Fin m) (nonloop : a e ≠ b e) (h : Fin q → ℝ) :
    (∑ φ, ∑ ψ, jointWeight D a b φ ψ * h (ψ e)) = ∑ i, D.probability i * h i := by
  classical
  have law (i : Fin q) :
      (∑ ω : (Fin t → Fin n) × (Fin m → Fin q),
        jointWeight D a b ω.1 ω.2 * (if ω.2 e = i then (1 : ℝ) else 0)) = D.probability i := by
    simp only [Fintype.sum_prod_type]
    exact single_edge_law D hn a b e nonloop i
  simpa only [Fintype.sum_prod_type] using integrate_single
    (fun ω : (Fin t → Fin n) × (Fin m → Fin q) => jointWeight D a b ω.1 ω.2)
    (fun ω => ω.2 e) D.probability law h

theorem nonincident_edge_expectation {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t)
    (e f : Fin m) (nonincident : Function.Injective ![a e, b e, a f, b f]) (h : Fin q → Fin q → ℝ) :
    (∑ φ, ∑ ψ, jointWeight D a b φ ψ * h (ψ e) (ψ f)) =
      ∑ i, ∑ j, (D.probability i * D.probability j) * h i j := by
  classical
  have law (i j : Fin q) :
      (∑ ω : (Fin t → Fin n) × (Fin m → Fin q), jointWeight D a b ω.1 ω.2 *
        ((if ω.2 e = i then (1 : ℝ) else 0) * (if ω.2 f = j then (1 : ℝ) else 0))) =
          D.probability i * D.probability j := by
    simp only [Fintype.sum_prod_type]
    exact nonincident_edge_law D hn a b e f nonincident i j
  simpa only [Fintype.sum_prod_type] using integrate_pair
    (fun ω : (Fin t → Fin n) × (Fin m → Fin q) => jointWeight D a b ω.1 ω.2)
    (fun ω => ω.2 e) (fun ω => ω.2 f) D.probability D.probability law h

/--
---
conclusion: Lax263307.CoupledSamplingBounds.total_length_expectation
---
Interchange the sums over outcomes and source edges, then use each
edge route’s marginal law to compute its expected size.
-/
theorem total_length_expectation {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t)
    (nonloop : ∀ e, a e ≠ b e) :
    (∑ φ, ∑ ψ, jointWeight D a b φ ψ * (∑ e, ((D.route (ψ e)).toFinset.card : ℝ))) =
      (m : ℝ) * Lax263307.PathSampling.expectedSize D.toSampling := by
  classical
  simp_rw [Finset.mul_sum]
  conv_lhs => arg 2; ext φ; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [single_edge_expectation D hn a b _ (nonloop _) (fun i => ((D.route i).toFinset.card : ℝ))]
  simp [Lax263307.PathSampling.expectedSize, Distribution.toSampling, nsmul_eq_mul]

theorem interaction_bound {n q : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Distribution G q) :
    (∑ i, ∑ j, (D.probability i * D.probability j) * (if Interaction G D i j then (1 : ℝ) else 0)) ≤
      Lax263307.PathSampling.collisionProbability D.toSampling +
        Lax263307.PathSampling.adjacencyProbability G D.toSampling := by
  classical
  unfold Lax263307.PathSampling.collisionProbability Lax263307.PathSampling.adjacencyProbability Distribution.toSampling
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  change (D.probability i * D.probability j) * (if Interaction G D i j then 1 else 0) ≤
    (if ¬Disjoint (D.route i).toFinset (D.route j).toFinset then D.probability i * D.probability j else 0) +
    (if ∃ u ∈ (D.route i).toFinset, ∃ v ∈ (D.route j).toFinset, G.Adj u v then D.probability i * D.probability j else 0)
  have hp := mul_nonneg (D.nonnegative i) (D.nonnegative j)
  by_cases hd : Disjoint (D.route i).toFinset (D.route j).toFinset <;>
    by_cases ha : ∃ u ∈ (D.route i).toFinset, ∃ v ∈ (D.route j).toFinset, G.Adj u v <;>
    simp only [Interaction, hd, ha, not_true_eq_false, not_false_eq_true, false_or, true_or,
      if_true, if_false, mul_one, mul_zero] <;> linarith

omit [DecidableEq J] in
theorem union_bound (w : Ω → ℝ) (nonnegative : ∀ ω, 0 ≤ w ω) (E : J → Ω → Prop) :
    (by classical exact ∑ ω, if ∃ j, E j ω then w ω else 0) ≤
      (by classical exact ∑ j, ∑ ω, if E j ω then w ω else 0) := by
  classical
  have hterm (ω : Ω) : (if ∃ j, E j ω then w ω else 0) ≤ ∑ j, if E j ω then w ω else 0 := by
    by_cases h : ∃ j, E j ω
    · obtain ⟨j, hj⟩ := h
      rw [if_pos ⟨j, hj⟩]
      have hs := Finset.single_le_sum (f := fun j => if E j ω then w ω else 0)
        (fun j _ => by split_ifs <;> first | exact nonnegative ω | exact le_refl 0) (Finset.mem_univ j)
      simpa only [if_pos hj] using hs
    · rw [if_neg h]
      apply Finset.sum_nonneg
      intro j _
      split_ifs <;> first | exact nonnegative ω | exact le_refl 0
  calc
    _ ≤ ∑ ω, ∑ j, if E j ω then w ω else 0 := Finset.sum_le_sum fun ω _ => hterm ω
    _ = _ := Finset.sum_comm

/--
---
conclusion: Lax263307.CoupledSamplingBounds.bad_probability_bound
---
Apply the union bound over ordered source-edge pairs. Every nonincident
pair has the independent route law; its interaction probability is at
most collision plus adjacency probability. There are at most m² pairs.
-/
theorem bad_probability_bound {n q t m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t) :
    badProbability G D a b ≤ (m : ℝ) ^ 2 *
      (Lax263307.PathSampling.collisionProbability D.toSampling +
        Lax263307.PathSampling.adjacencyProbability G D.toSampling) := by
  classical
  let Ω := (Fin t → Fin n) × (Fin m → Fin q)
  let w : Ω → ℝ := fun ω => jointWeight D a b ω.1 ω.2
  let E : (Fin m × Fin m) → Ω → Prop := fun ef ω =>
    Function.Injective ![a ef.1, b ef.1, a ef.2, b ef.2] ∧ Interaction G D (ω.2 ef.1) (ω.2 ef.2)
  have hnneg := (joint_normalized D hn a b).1
  have hu := union_bound w (fun ω => hnneg _ _) E
  have hbad : badProbability G D a b ≤ ∑ ef : Fin m × Fin m, ∑ ω : Ω,
      if E ef ω then w ω else 0 := by
    simpa only [Ω, E, w, badProbability, Fintype.sum_prod_type, Prod.exists] using hu
  have hpair (ef : Fin m × Fin m) : (∑ ω : Ω, if E ef ω then w ω else 0) ≤
      Lax263307.PathSampling.collisionProbability D.toSampling +
        Lax263307.PathSampling.adjacencyProbability G D.toSampling := by
    by_cases hi : Function.Injective ![a ef.1, b ef.1, a ef.2, b ef.2]
    · have heq : (∑ ω : Ω, if E ef ω then w ω else 0) =
          ∑ φ, ∑ ψ, jointWeight D a b φ ψ *
            (if Interaction G D (ψ ef.1) (ψ ef.2) then (1 : ℝ) else 0) := by
        simp [Ω, E, w, Fintype.sum_prod_type, hi, mul_ite]
      rw [heq, nonincident_edge_expectation D hn a b _ _ hi (fun i j => if Interaction G D i j then (1 : ℝ) else 0)]
      exact interaction_bound G D
    · have hz : (∑ ω : Ω, if E ef ω then w ω else 0) = 0 := by simp [E, hi]
      rw [hz]
      apply le_trans (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) (interaction_bound G D)
      split_ifs <;> simp only [mul_one, mul_zero] <;>
        first | exact mul_nonneg (D.nonnegative _) (D.nonnegative _) | exact le_refl 0
  calc
    _ ≤ ∑ ef : Fin m × Fin m, ∑ ω : Ω, if E ef ω then w ω else 0 := hbad
    _ ≤ ∑ _ef : Fin m × Fin m,
        (Lax263307.PathSampling.collisionProbability D.toSampling +
          Lax263307.PathSampling.adjacencyProbability G D.toSampling) :=
      Finset.sum_le_sum fun ef _ => hpair ef
    _ = _ := by simp [sq, nsmul_eq_mul]; ring

theorem finite_good_outcome (w : Ω → ℝ) (nonnegative : ∀ ω, 0 ≤ w ω)
    (normalized : (∑ ω, w ω) = 1) (bad : Ω → Prop) (cost : Ω → ℝ)
    (cost_nonnegative : ∀ ω, 0 ≤ cost ω) (M : ℝ) (positive : 0 < M)
    (bad_bound : (by classical exact ∑ ω, if bad ω then w ω else 0) ≤ (1 / 4 : ℝ))
    (expected_bound : (∑ ω, w ω * cost ω) ≤ M) :
    ∃ ω, 0 < w ω ∧ ¬bad ω ∧ cost ω ≤ 4 * M := by
  classical
  let q := Fintype.card Ω
  let e : Ω ≃ Fin q := Fintype.equivFin Ω
  let P : Lax263307.PathSampling.Distribution 0 q := {
    probability := fun i => w (e.symm i)
    nonnegative := fun i => nonnegative _
    normalized := (e.symm.sum_comp w).trans normalized
    vertices := fun _ => ∅ }
  have hbad : Lax263307.SamplingOutcomes.eventProbability P {i | bad (e.symm i)} ≤ 1 / 4 := by
    unfold Lax263307.SamplingOutcomes.eventProbability
    change (∑ i, if bad (e.symm i) then w (e.symm i) else 0) ≤ _
    rw [e.symm.sum_comp (fun ω => if bad ω then w ω else 0)]
    exact bad_bound
  have hexpected : (∑ i, P.probability i * cost (e.symm i)) ≤ M := by
    change (∑ i, (fun ω => w ω * cost ω) (e.symm i)) ≤ M
    exact (e.symm.sum_comp (fun ω => w ω * cost ω)).trans_le expected_bound
  obtain ⟨i, hi, hgood, hcost⟩ := Lax263307.SamplingOutcomes.good_outcome P
    {i | bad (e.symm i)} (fun i => cost (e.symm i)) M positive
      (fun i => cost_nonnegative _) hbad hexpected
  exact ⟨e.symm i, hi, hgood, hcost⟩

/--
---
conclusion: Lax263307.CoupledSamplingBounds.good_route_sample
---
Reindex the finite coupled outcome space by Fin and apply the proved
good-outcome lemma to the bad interaction event and total route size.
The probability and length estimates provide its two bounds.
-/
theorem good_route_sample {n q t m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t) (nonloop : ∀ e, a e ≠ b e)
    (M : ℝ) (positive : 0 < M)
    (bad_budget : (m : ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling) ≤ 1 / 4)
    (length_budget : (m : ℝ) * Lax263307.PathSampling.expectedSize D.toSampling ≤ M) :
    ∃ φ : Fin t → Fin n, ∃ ψ : Fin m → Fin q,
      0 < jointWeight D a b φ ψ ∧
      (∀ e f, Function.Injective ![a e, b e, a f, b f] → ¬Interaction G D (ψ e) (ψ f)) ∧
      (∑ e, ((D.route (ψ e)).toFinset.card : ℝ)) ≤ 4 * M := by
  classical
  let Ω := (Fin t → Fin n) × (Fin m → Fin q)
  let w : Ω → ℝ := fun ω => jointWeight D a b ω.1 ω.2
  let bad : Ω → Prop := fun ω =>
    ∃ e f, Function.Injective ![a e, b e, a f, b f] ∧ Interaction G D (ω.2 e) (ω.2 f)
  let cost : Ω → ℝ := fun ω => ∑ e, ((D.route (ω.2 e)).toFinset.card : ℝ)
  have hnneg := joint_normalized D hn a b
  have hnormalized : (∑ ω : Ω, w ω) = 1 := by
    simpa only [Ω, w, Fintype.sum_prod_type] using hnneg.2
  have hbad : (∑ ω : Ω, if bad ω then w ω else 0) ≤ 1 / 4 := by
    have h := (bad_probability_bound G D hn a b).trans bad_budget
    simpa only [badProbability, Ω, bad, w, Fintype.sum_prod_type] using h
  have hexpected : (∑ ω : Ω, w ω * cost ω) ≤ M := by
    simpa only [Ω, w, cost, Fintype.sum_prod_type, total_length_expectation D hn a b nonloop] using length_budget
  obtain ⟨ω, hp, hg, hc⟩ := finite_good_outcome w (fun ω => hnneg.1 _ _) hnormalized bad cost
    (fun ω => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) M positive
    (by
      convert hbad using 1
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : bad ω <;> simp [h]) hexpected
  refine ⟨ω.1, ω.2, hp, ?_, hc⟩
  intro e f hef hint
  exact hg ⟨e, f, hef, hint⟩


end Lax263307Proofs.CoupledSamplingBounds
