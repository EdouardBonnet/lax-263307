import Lax263307.NoBoundedLoadRoutes
import Lax263307Proofs.TreeExtensions
import Mathlib.Tactic

namespace Lax263307Proofs.NoBoundedLoadRoutes

open Lax263307.GraphClasses Lax263307.PowerBagBounds Lax228581.Treewidth
open Lax263307.InducedEmbeddingWidth Lax263307Proofs.TreeExtensions

theorem edgeless_width_zero {t : ℕ} (H : SimpleGraph (Fin t))
    (edgeless : ∀ v u, ¬H.Adj v u) : treewidth H = 0 := by
  classical
  let S : Set (Fin t) := ∅
  let D : TreeDecomposition (H.induce S) := {
    Node := Unit
    tree := ⊥
    isTree := SimpleGraph.IsTree.of_subsingleton
    bag := fun _ => ∅
    vertex_mem_bag := fun v => False.elim v.property
    edge_mem_bag := by intro u _ _; exact False.elim u.property
    bag_indices_connected := fun v => False.elim v.property }
  have hisolated (v : Fin t) (_ : v ∉ S) : H.IsIsolated v := edgeless v
  have hwidth : HasTreewidthAtMost H 0 := by
    refine ⟨extendIsolated S hisolated D, ?_⟩
    exact extendIsolated_card S hisolated D 1 (le_refl _) (fun _ => by simp [D])
  exact Nat.le_zero.mp (Nat.sInf_le hwidth)

theorem subcubic_edges {t : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (degree_bound : ∀ v, H.degree v ≤ 3) : H.edgeSet.ncard ≤ 2 * t := by
  classical
  have hsum : (∑ v, H.degree v) ≤ ∑ _v : Fin t, 3 := Finset.sum_le_sum fun v _ => degree_bound v
  rw [H.sum_degrees_eq_twice_card_edges, H.edgeFinset_card, Set.fintypeCard_eq_ncard] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

theorem scale_square (c b a : ℕ) :
    8 * (c * b ^ (2 * a)) ^ 2 * b ^ 2 = 8 * c ^ 2 * b ^ (4 * a + 2) := by
  calc
    _ = 8 * c ^ 2 * (b ^ ((2 * a) * 2) * b ^ 2) := by rw [mul_pow, ← pow_mul]; ring
    _ = _ := by rw [← pow_add, show (2 * a) * 2 + 2 = 4 * a + 2 by omega]

/--
---
conclusion: Lax263307.NoBoundedLoadRoutes.no_bounded_load_routes
---
Choose a controlled-size subcubic source above the growth threshold.
The overshoot and degree bound give a polynomial bound on its edge count,
so the target and sparsity hypotheses meet the sampling budgets. Apply
the cost-based width obstruction, then the integer growth inequality.
It bounds the source order below its requested lower bound, a contradiction.
-/
theorem no_bounded_load_routes (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (a_positive : 0 < a) (A_positive : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ K : ℕ, 0 < K ∧ ∀ (n q : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → ∀ (D : Lax263307.RouteDistributions.Distribution G q), 0 < n →
      ∀ (ℓ : ℕ), 0 < ℓ → ∀ (x : Fin n → ℝ) (k p : ℝ), 0 < k → 0 < p →
      (∀ v, 0 ≤ x v ∧ x v ≤ 1) → (∑ v, x v) ≤ k →
      (∀ v, Lax263307.PathSampling.load D.toSampling v ≤ (ℓ : ℝ) * x v / k) →
      Lax263307.Entropy.edgeCost G x ≤ k ^ 2 / p →
      (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ k →
      (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) ≤ p → False := by
  classical
  obtain ⟨CW, CS, hCW, hCS, family⟩ := Lax263307.SourceGraphs.controlled_family
  obtain ⟨hmonotone, hclass, hWpositive, hWpower⟩ := root_bag_bound C a A a_positive A_positive class_bound
  let W := bagBound a A
  let T := Lax263307.WidthGrowth.threshold a A CW
  let scale := 2 * CS * (T + CW + 3)
  let K := 8 * scale ^ 2 + 1
  refine ⟨K, Nat.zero_lt_succ _, ?_⟩
  intro n q G _ hG D hn ℓ hℓ x k p hk hp hcost hmass hload hedge htarget hsparse
  let request := (T + CW + 1) * (ℓ + 1) ^ (2 * a) + 1
  obtain ⟨t, H, hrequest, hsize, hsubcubic, hlinear⟩ := family request
  have hpw : 1 ≤ (ℓ + 1) ^ (2 * a) := Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos ℓ))
  have hgreater : CW < t := by
    have h := Nat.mul_le_mul_left (T + CW + 1) hpw
    change (T + CW + 1) * 1 ≤ (T + CW + 1) * (ℓ + 1) ^ (2 * a) at h
    dsimp [request] at hrequest
    omega
  have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le CW) hgreater
  have hdeg (v : Fin t) : H.degree v ≤ 3 := by
    rw [← H.card_neighborSet_eq_degree v, Set.fintypeCard_eq_ncard]
    exact hsubcubic v
  have hmpos : 0 < H.edgeSet.ncard := by
    by_contra h
    have hz : H.edgeSet.ncard = 0 := by omega
    have hnone : ∀ v u, ¬H.Adj v u := by
      intro v u h
      have hh : 0 < H.edgeSet.ncard := (Set.ncard_pos (Set.toFinite H.edgeSet)).mpr ⟨s(v, u), h⟩
      omega
    rw [edgeless_width_zero H hnone, zero_add, mul_one] at hlinear
    omega
  have hmedges := subcubic_edges H hdeg
  have hrequestcap : request + 1 ≤ (T + CW + 3) * (ℓ + 1) ^ (2 * a) := by
    dsimp [request]
    nlinarith
  have hmcap : H.edgeSet.ncard ≤ scale * (ℓ + 1) ^ (2 * a) := by
    calc
      _ ≤ 2 * t := hmedges
      _ ≤ 2 * (CS * (request + 1)) := Nat.mul_le_mul_left 2 hsize
      _ ≤ 2 * (CS * ((T + CW + 3) * (ℓ + 1) ^ (2 * a))) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left CS hrequestcap)
      _ = _ := by dsimp [scale]; ring
  have hbudget : 8 * H.edgeSet.ncard ^ 2 * ℓ ^ 2 ≤ K * (ℓ + 1) ^ (4 * a + 2) := by
    calc
      _ ≤ 8 * (scale * (ℓ + 1) ^ (2 * a)) ^ 2 * (ℓ + 1) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hmcap _)) (Nat.pow_le_pow_left (Nat.le_succ ℓ) _)
      _ = 8 * scale ^ 2 * (ℓ + 1) ^ (4 * a + 2) := scale_square _ _ _
      _ ≤ _ := Nat.mul_le_mul_right _ (by dsimp [K]; omega)
  have hbudget₂ : 16 * H.edgeSet.ncard ^ 2 * ℓ ^ 2 ≤ (2 * K) * (ℓ + 1) ^ (4 * a + 2) := by
    have h := Nat.mul_le_mul_left 2 hbudget
    convert h using 1 <;> ring
  have htarget' : 8 * (H.edgeSet.ncard : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 ≤ k := by
    have h : 8 * (H.edgeSet.ncard : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 ≤ (K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) := by exact_mod_cast hbudget
    exact h.trans htarget
  have hsparse' : 16 * (H.edgeSet.ncard : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 ≤ p := by
    have h : 16 * (H.edgeSet.ncard : ℝ) ^ 2 * (ℓ : ℝ) ^ 2 ≤ (2 * K : ℝ) * ((ℓ : ℝ) + 1) ^ (4 * a + 2) := by exact_mod_cast hbudget₂
    exact h.trans hsparse
  obtain ⟨removed, hremoved, hwidth⟩ := Lax263307.CostSamplingObstruction.cost_width_obstruction
    C hereditary W hmonotone hclass H G hG D hn 3 (24 * CW * ℓ) hdeg hmpos x k ℓ p hk
      (by exact_mod_cast hℓ) hp hcost hmass hload hedge htarget' hsparse'
  have hr : (24 * CW * ℓ) * removed ≤ 4 * H.edgeSet.ncard * ℓ := by exact_mod_cast hremoved
  have hw : t ≤ CW * (max 1 (6 * W (3 * H.edgeSet.ncard * (24 * CW * ℓ) ^ 2)) + removed) := by
    exact hlinear.trans (Nat.mul_le_mul_left CW hwidth)
  have horder := Lax263307.WidthGrowth.order_bound a A CW ℓ t H.edgeSet.ncard removed a_positive hℓ
    htpos W hWpositive hWpower hmedges hr hw
  have hpower : ℓ ^ (2 * (a - 1)) ≤ (ℓ + 1) ^ (2 * a) := by
    exact (Nat.pow_le_pow_left (Nat.le_succ ℓ) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos ℓ) (by omega))
  have hsmall : t ≤ (T + CW + 1) * (ℓ + 1) ^ (2 * a) := by
    calc
      t ≤ T * ℓ ^ (2 * (a - 1)) := horder
      _ ≤ T * (ℓ + 1) ^ (2 * a) := Nat.mul_le_mul_left T hpower
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  dsimp [request] at hrequest
  omega


end Lax263307Proofs.NoBoundedLoadRoutes
