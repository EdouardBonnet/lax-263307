import Lax263307.RouteDistributions
import Lax263307Proofs.SplitPathProjection
import Lax455465.ArcToPath
import Mathlib.Tactic

namespace Lax263307Proofs.RouteDistributions

open Lax263307.RouteDistributions

noncomputable def tripleEquiv (n q : ℕ) : Fin (n * (n * q)) ≃ Fin n × (Fin n × Fin q) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

theorem sum_triples {n q : ℕ} (f : Fin n × (Fin n × Fin q) → ℝ) :
    (∑ j, f (tripleEquiv n q j)) = ∑ u, ∑ v, ∑ i, f (u, v, i) := by
  rw [(tripleEquiv n q).sum_comp]
  simp only [Fintype.sum_prod_type]

open Lax263307.RoutingNormalization

/--
---
conclusion: Lax263307.RouteDistributions.finite_routes
---
Index outcomes by the endpoint pair and the original flow record. The
normalization theorem gives total mass one. Endpoint uniqueness makes the
endpoint marginal uniform; the load theorem bounds each membership feature.
-/
theorem finite_routes {n q : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (w : Fin q → ℝ) (E : Fin n → Fin n → Fin q → Prop)
    (w_nonnegative : ∀ i, 0 ≤ w i) (γ : ℝ) (γ_positive : 0 < γ)
    (lower : ∀ u v, 1 / γ ≤ routed w E u v)
    (Q : Fin q → List (Fin n))
    (routes : ∀ u v i, E u v i → (Q i).Nodup ∧ (Q i).IsChain G.Adj ∧
      (Q i).head? = some u ∧ (Q i).getLast? = some v) :
    ∃ D : Distribution G (n * (n * q)), ∀ z,
      Lax263307.PathSampling.load D.toSampling z ≤ γ / (n : ℝ) ^ 2 *
        (∑ i, w i * (if z ∈ Q i then (1 : ℝ) else 0)) := by
  classical
  have positive (u v : Fin n) : 0 < routed w E u v :=
    lt_of_lt_of_le (by positivity) (lower u v)
  obtain ⟨hp, hpair, htotal⟩ := normalization_correct w E hn w_nonnegative positive
  have unique : IsUniquePair E := by
    intro i u v u' v' h h'
    have hends := routes u v i h
    have hends' := routes u' v' i h'
    exact ⟨Option.some.inj (hends.2.2.1.symm.trans hends'.2.2.1),
      Option.some.inj (hends.2.2.2.symm.trans hends'.2.2.2)⟩
  let p : Fin n × (Fin n × Fin q) → ℝ := fun a => probability w E a.1 a.2.1 a.2.2
  have hvalid (u v : Fin n) (i : Fin q) (h : 0 < probability w E u v i) : E u v i := by
    by_contra hE
    simp [probability, hE] at h
  have huniform (s t : Fin n) :
      (∑ u, ∑ v, ∑ i, if (Q i).head? = some s ∧ (Q i).getLast? = some t then
        probability w E u v i else 0) = 1 / (n : ℝ) ^ 2 := by
    have hterm (u v : Fin n) (i : Fin q) :
        (if (Q i).head? = some s ∧ (Q i).getLast? = some t then probability w E u v i else 0) =
        (if u = s ∧ v = t then probability w E u v i else 0) := by
      by_cases hE : E u v i
      · obtain ⟨_, _, hstart, hfinish⟩ := routes u v i hE
        simp only [hstart, hfinish, Option.some.injEq]
      · simp [probability, hE]
    simp_rw [hterm, ite_and]
    simpa using hpair s t
  let D : Distribution G (n * (n * q)) := {
    probability := fun j => p (tripleEquiv n q j)
    nonnegative := fun j => hp _ _ _
    normalized := by
      rw [sum_triples]
      exact htotal
    route := fun j => Q (tripleEquiv n q j).2.2
    valid := by
      intro j hj
      have he := hvalid _ _ _ hj
      have h := routes _ _ _ he
      refine ⟨h.1, h.2.1, ?_⟩
      intro hnil
      have hstart := h.2.2.1
      simp [hnil] at hstart
    uniform := by
      intro s t
      rw [sum_triples (fun a => if (Q a.2.2).head? = some s ∧
        (Q a.2.2).getLast? = some t then p a else 0)]
      exact huniform s t }
  refine ⟨D, ?_⟩
  intro z
  have hload : Lax263307.PathSampling.load D.toSampling z =
      ∑ u, ∑ v, ∑ i, probability w E u v i * (if z ∈ Q i then (1 : ℝ) else 0) := by
    unfold Lax263307.PathSampling.load Distribution.toSampling
    change (∑ j, if z ∈ (Q (tripleEquiv n q j).2.2).toFinset then
      p (tripleEquiv n q j) else 0) = _
    rw [sum_triples (fun a => if z ∈ (Q a.2.2).toFinset then p a else 0)]
    simp only [List.mem_toFinset]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro i _
    dsimp [p]
    split_ifs <;> simp
  rw [hload]
  apply normalized_load_bound w E hn w_nonnegative unique γ γ_positive lower
  intro i
  split_ifs <;> norm_num

open scoped NNReal NNRat
open Lax263307.VertexSplitting Lax263307.SplitPathProjection
open Lax455465.ConcurrentFlow Lax455465.ProductNetwork

theorem split_path_distribution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 0 < n) (x : Fin n → ℚ≥0) (large : ℚ≥0) (γ : ℝ) (γ_positive : 0 < γ)
    (f : ℝ≥0) (high : 1 / γ ≤ (f : ℝ)) (F : PathFlow (2 * n))
    (feasible : IsConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights f F) :
    ∃ q, ∃ D : Distribution G q, ∀ z,
      Lax263307.PathSampling.load D.toSampling z ≤ γ * (x z : ℝ) / (n : ℝ) ^ 2 := by
  classical
  let ι := ↥F.support
  let q := Fintype.card ι
  let e : ι ≃ Fin q := Fintype.equivFin ι
  let P : Fin q → List (Fin (2 * n)) := fun i => (e.symm i).val
  let w : Fin q → ℝ := fun i => (F (P i) : ℝ)
  let E : Fin n → Fin n → Fin q → Prop := fun u v i =>
    (P i).head? = some (minus u) ∧ (P i).getLast? = some (plus v)
  have member (i : Fin q) : P i ∈ F.support := (e.symm i).property
  have sum_paths (a : List (Fin (2 * n)) → ℝ) :
      (∑ i, a (P i)) = ∑ R ∈ F.support, a R := by
    change (∑ i, (fun j : ι => a j.val) (e.symm i)) = _
    exact (e.symm.sum_comp (fun j : ι => a j.val)).trans (Finset.sum_coe_sort F.support a)
  have lower (u v : Fin n) : 1 / γ ≤ Lax263307.RoutingNormalization.routed w E u v := by
    have hdemand := feasible.2.2 (minus u) (plus v)
      (Lax263307Proofs.SplitPathProjection.minus_ne_plus u v)
    have hdemand' : f ≤ Lax455465.ConcurrentFlow.routed F (minus u) (plus v) := by
      simpa [pairDemand, splitInstance, Lax455465.RationalEncoding.RationalInstance.weights] using hdemand
    have hrouted : Lax263307.RoutingNormalization.routed w E u v =
        (Lax455465.ConcurrentFlow.routed F (minus u) (plus v) : ℝ) := by
      unfold Lax263307.RoutingNormalization.routed Lax455465.ConcurrentFlow.routed
      push_cast
      simp only [apply_ite (fun a : ℝ≥0 => (a : ℝ)), NNReal.coe_zero]
      rw [← sum_paths (fun R => if R.head? = some (minus u) ∧ R.getLast? = some (plus v)
        then (F R : ℝ) else 0)]
      apply Finset.sum_congr rfl
      intro i _
      simp only [E, w]
    rw [hrouted]
    exact high.trans (by exact_mod_cast hdemand')
  have projections (i : Fin q) (h : ∃ u v, E u v i) :
      ∃ Q : List (Fin n), P i = expandRoute Q ∧ Q.Nodup ∧ Q.IsChain G.Adj ∧
        (∃ u v, E u v i ∧ Q.head? = some u ∧ Q.getLast? = some v) := by
    obtain ⟨u, v, hs, ht⟩ := h
    obtain ⟨Q, hP, hsimple, hchain, hhead, hlast⟩ :=
      Lax263307.SplitPathProjection.split_support_projection G x large f F feasible (P i)
        (member i) u v hs ht
    exact ⟨Q, hP, hsimple, hchain, u, v, ⟨hs, ht⟩, hhead, hlast⟩
  let Q : Fin q → List (Fin n) := fun i =>
    if h : ∃ u v, E u v i then Classical.choose (projections i h) else []
  have route_spec (i : Fin q) (h : ∃ u v, E u v i) :
      P i = expandRoute (Q i) ∧ (Q i).Nodup ∧ (Q i).IsChain G.Adj ∧
        (∃ u v, E u v i ∧ (Q i).head? = some u ∧ (Q i).getLast? = some v) := by
    dsimp only [Q]
    rw [dif_pos h]
    exact Classical.choose_spec (projections i h)
  have routes (u v : Fin n) (i : Fin q) (h : E u v i) :
      (Q i).Nodup ∧ (Q i).IsChain G.Adj ∧
        (Q i).head? = some u ∧ (Q i).getLast? = some v := by
    obtain ⟨hP, hsimple, hchain, s, t, hE, hs, ht⟩ := route_spec i ⟨u, v, h⟩
    have hu : s = u := Lax263307Proofs.SplitPathProjection.minus_injective n
      (Option.some.inj (hE.1.symm.trans h.1))
    have hv : t = v := Lax263307Proofs.SplitPathProjection.plus_injective n
      (Option.some.inj (hE.2.symm.trans h.2))
    exact ⟨hsimple, hchain, hu ▸ hs, hv ▸ ht⟩
  obtain ⟨D, hD⟩ := Lax263307.RouteDistributions.finite_routes G hn w E (fun i => NNReal.coe_nonneg _) γ γ_positive lower Q routes
  refine ⟨_, D, ?_⟩
  intro z
  have hterm (i : Fin q) :
      w i * (if z ∈ Q i then (1 : ℝ) else 0) ≤
        (F (P i) : ℝ) * (((P i).zip (P i).tail).count (minus z, plus z) : ℝ) := by
    by_cases h : ∃ u v, E u v i
    · obtain ⟨hP, hsimple, _⟩ := route_spec i h
      rw [hP, Lax263307.SplitPathProjection.capacity_arc_count (Q i) hsimple z]
      dsimp [w]
      rw [hP]
      split_ifs <;> simp
    · have hQ : Q i = [] := by simp [Q, h]
      simp only [hQ, List.not_mem_nil, if_false, mul_zero]
      positivity
  have hsum : (∑ i, w i * (if z ∈ Q i then (1 : ℝ) else 0)) ≤
      (arcLoad F (minus z) (plus z) : ℝ) := by
    calc
      _ ≤ ∑ i, (F (P i) : ℝ) * (((P i).zip (P i).tail).count (minus z, plus z) : ℝ) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = (arcLoad F (minus z) (plus z) : ℝ) := by
        rw [sum_paths (fun R => (F R : ℝ) * ((R.zip R.tail).count (minus z, plus z) : ℝ))]
        simp [arcLoad]
  have hcapacity : (arcLoad F (minus z) (plus z) : ℝ) ≤ (x z : ℝ) := by
    have h := feasible.2.1 (minus z) (plus z)
    change arcLoad F (minus z) (plus z) ≤ ((splitInstance G x large).capacity (minus z) (plus z) : ℝ≥0) at h
    rw [Lax263307Proofs.VertexSplitting.capacity_minus] at h
    simp only at h
    exact_mod_cast h
  calc
    _ ≤ γ / (n : ℝ) ^ 2 * (∑ i, w i * (if z ∈ Q i then (1 : ℝ) else 0)) := hD z
    _ ≤ γ / (n : ℝ) ^ 2 * (x z : ℝ) :=
      mul_le_mul_of_nonneg_left (hsum.trans hcapacity) (by positivity)
    _ = _ := by ring

/--
---
conclusion: Lax263307.RouteDistributions.split_arc_distribution
---
Apply the registered arc-to-path theorem. Enumerate the finite path-flow
support, retain the minus-to-plus commodities, and choose their projected
graph routes. Each retained commodity has routed mass at least 1/gamma.
The capacity-arc count bounds the weighted membership feature by the
original split flow's arc load, which is at most the vertex capacity.
-/
theorem split_arc_distribution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 0 < n) (x : Fin n → ℚ≥0) (large : ℚ≥0) (γ : ℝ) (γ_positive : 0 < γ)
    (f : ℝ≥0) (high : 1 / γ ≤ (f : ℝ)) (F : ArcFlow (2 * n))
    (feasible : IsArcConcurrentFlow .directed (splitInstance G x large).network
      (splitInstance G x large).weights f F) :
    ∃ q, ∃ D : Distribution G q, ∀ z,
      Lax263307.PathSampling.load D.toSampling z ≤ γ * (x z : ℝ) / (n : ℝ) ^ 2 := by
  obtain ⟨P, hP, _⟩ := Lax455465.ArcToPath.exists_path_flow .directed
    (splitInstance G x large).network (splitInstance G x large).weights f F feasible
  exact split_path_distribution G hn x large γ γ_positive f high P hP


end Lax263307Proofs.RouteDistributions
