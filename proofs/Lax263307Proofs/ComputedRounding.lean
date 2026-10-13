import Lax263307.ComputedRounding
import Mathlib.Tactic

namespace Lax263307Proofs.ComputedRounding

open Lax263307.ComputedRounding Lax263307.LinearRelaxation Lax263307.SeparatorComponents
open Lax263307.ComponentCutEncoding

theorem target_bounds (δ c : ℚ) (hδ : δ ≤ 1) (hc : 0 ≤ c) :
    (1 - δ) * c < (target δ c : ℚ) ∧ (target δ c - 1 : ℕ) ≤ (1 - δ) * c := by
  constructor
  · simpa only [target, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one ((1 - δ) * c)
  · simpa only [target, Nat.add_sub_cancel] using
      Nat.floor_le (mul_nonneg (sub_nonneg.mpr hδ) hc)

/--
---
conclusion: Lax263307.ComputedRounding.collect_correct
---
Inspect the actual first failed query. Its certified independence bound and
rational target give the buffered component gap. If no query fails, skipped
parts contribute the empty set and the successful answers satisfy the proved
heavy-part union bound.
-/
theorem collect_correct {n r : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (k h : ℕ) (δ : ℚ) (η : ℝ)
    (hn : 0 < n) (hk : 0 < k) (hδ : 0 < δ) (small : δ ≤ 1 / 4) (hη : 0 < η)
    (x y : MomentVector n r) (feasible : IsFeasible G k r y)
    (A S : Finset (Fin n)) (P : Partition G S ι) (size : A.card ≤ r)
    (moment : η ≤ value y A) (count : Fintype.card ι ≤ 2 * n)
    (light : ∑ v ∈ S, conditioned y A v ≤ (δ : ℝ) * k)
    (order : List ι) (complete : ∀ i, i ∈ order)
    (c : ι → ℚ) (cost_cast : ∀ i, (c i : ℝ) = ∑ v ∈ P.vertices i, conditioned y A v)
    (query : ι → ℕ → Option (Finset (Fin n)))
    (queries : ∀ i, δ * k / (4 * n) < c i →
      match query i (target δ (c i)) with
      | some I => I ⊆ P.vertices i ∧ G.IsIndepSet (I : Set (Fin n)) ∧
          (1 - 4 * (δ : ℝ)) ^ h * (target δ (c i) : ℝ) ≤ I.card
      | none => IsIndependenceBound G (P.vertices i) (target δ (c i) - 1))
    (near : ∀ B, |x B - y B| ≤ η * (δ : ℝ) ^ 2 / (32 * (n : ℝ) ^ 2)) :
    match collect order P.vertices δ k c query with
    | .found I => G.IsIndepSet (I : Set (Fin n)) ∧
        (1 - 4 * (δ : ℝ)) ^ (h + 1) * (k : ℝ) ≤ I.card
    | .cut C u => u ≤ n ∧ IsIndependenceBound G C u ∧
        (∀ z ∈ independentSetHull G k r, evaluate (coefficient A C u) z ≤ 0) ∧
        η * (δ : ℝ) ^ 2 / (16 * n) ≤ evaluate (coefficient A C u) x ∧
        (∑ B : Coordinate n r, |(coefficient A C u B : ℝ)|) ≤ 2 * n := by
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hsmallR : (δ : ℝ) ≤ 1 / 4 := by
    have hs : (δ : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr small
    norm_num at hs ⊢
    exact hs
  have hinv := Lax263307.ConditionedCosts.conditioning_invariants G k r y feasible A size
    (hη.trans_le moment)
  have hc0 (i : ι) : (0 : ℝ) ≤ c i := by
    rw [cost_cast]
    exact Finset.sum_nonneg (fun v _ => (hinv.1 v).1)
  have hc1 (i : ι) : (c i : ℝ) ≤ (P.vertices i).card := by
    rw [cost_cast]
    simpa using Finset.sum_le_sum (fun v (_ : v ∈ P.vertices i) => (hinv.1 v).2)
  have ht (i : ι) : (1 - (δ : ℝ)) * (c i : ℝ) < (target δ (c i) : ℝ) ∧
      (target δ (c i) - 1 : ℕ) ≤ (1 - (δ : ℝ)) * (c i : ℝ) := by
    have ht := target_bounds δ (c i) (by linarith) (by exact_mod_cast hc0 i)
    exact_mod_cast ht
  have active_iff (i : ι) : δ * k / (4 * n) < c i ↔
      (δ : ℝ) * k / (4 * n) < ∑ v ∈ P.vertices i, conditioned y A v := by
    rw [← cost_cast]
    norm_cast
  unfold collect
  cases hfind : order.find? (fun i => (answer δ k c query i).isNone) with
  | some i =>
    have hnone : answer δ k c query i = none := by
      simpa only [Option.isNone_iff_eq_none] using List.find?_some hfind
    have hactive : δ * k / (4 * n) < c i := by
      by_contra hfalse
      simp only [answer, if_neg hfalse] at hnone
      contradiction
    have hquery : query i (target δ (c i)) = none := by
      simpa only [answer, if_pos hactive] using hnone
    have hbound := queries i hactive
    rw [hquery] at hbound
    have hcard : (P.vertices i).card ≤ n := (P.vertices i).card_le_univ.trans_eq (Fintype.card_fin n)
    have hupper : target δ (c i) - 1 ≤ n := by
      have hupperR : (target δ (c i) - 1 : ℕ) ≤ (n : ℝ) := by
        have hcardR : ((P.vertices i).card : ℝ) ≤ n := by exact_mod_cast hcard
        nlinarith only [(ht i).2, hc0 i, hc1 i, hδR, hcardR]
      exact_mod_cast hupperR
    have hheavy : ((δ : ℝ) / 2) * k / (2 * n) ≤ ∑ v ∈ P.vertices i, conditioned y A v := by
      have heq : ((δ : ℝ) / 2) * k / (2 * n) = (δ : ℝ) * k / (4 * n) := by ring
      rw [heq]
      exact ((active_iff i).mp hactive).le
    have hround : (target δ (c i) - 1 : ℕ) ≤
        (1 - (δ : ℝ) / 2) * ∑ v ∈ P.vertices i, conditioned y A v := by
      rw [← cost_cast]
      nlinarith only [(ht i).2, hc0 i, hδR]
    have hnear : ∀ B, |x B - y B| ≤ η * ((δ : ℝ) / 2) ^ 2 / (8 * (n : ℝ) ^ 2) := by
      intro B
      convert near B using 1
      ring
    obtain ⟨hvalid, hgap⟩ := Lax263307.StrongComponentGaps.query_gap G k x y A (P.vertices i)
      (target δ (c i) - 1) size hbound hupper η ((δ : ℝ) / 2) hη (by linarith) hn hk
      moment hheavy hround hnear
    refine ⟨hupper, hbound, hvalid, ?_, ?_⟩
    · convert hgap using 1
      ring
    · apply (Lax263307.StrongComponentGaps.coefficient_l1 A (P.vertices i) (target δ (c i) - 1)).trans
      exact_mod_cast (show (P.vertices i).card + (target δ (c i) - 1) ≤ 2 * n by omega)
  | none =>
    have hsome (i : ι) : ∃ I, answer δ k c query i = some I := by
      have hi := List.find?_eq_none.mp hfind i (complete i)
      cases he : answer δ k c query i with
      | none => simp only [he, Option.isNone_none] at hi; contradiction
      | some I => exact ⟨I, rfl⟩
    let I : ι → Finset (Fin n) := fun i => (answer δ k c query i).getD ∅
    have hlegal (i : ι) : I i ⊆ P.vertices i ∧ G.IsIndepSet (I i : Set (Fin n)) := by
      by_cases hactive : δ * k / (4 * n) < c i
      · obtain ⟨J, hJ⟩ := hsome i
        have hq : query i (target δ (c i)) = some J := by simpa only [answer, if_pos hactive] using hJ
        have hs := queries i hactive
        rw [hq] at hs
        have hI : I i = J := by simp only [I, hJ, Option.getD_some]
        rw [hI]
        exact ⟨hs.1, hs.2.1⟩
      · have hI : I i = ∅ := by simp only [I, answer, if_neg hactive, Option.getD_some]
        rw [hI]
        exact ⟨Finset.empty_subset _, by intro a ha; simp at ha⟩
    apply Lax263307.HeavyRecursiveRounding.heavy_union_size G S P (conditioned y A) k h δ
      hn hδR.le hsmallR count hinv.2.1 light I (fun i => target δ (c i))
      (fun i => (hlegal i).1) (fun i => (hlegal i).2)
    · intro i _
      rw [← cost_cast]
      exact (ht i).1
    · intro i hi
      have hactive := (active_iff i).mpr hi
      obtain ⟨J, hJ⟩ := hsome i
      have hq : query i (target δ (c i)) = some J := by simpa only [answer, if_pos hactive] using hJ
      have hs := queries i hactive
      rw [hq] at hs
      simpa only [I, hJ, Option.getD_some] using hs.2.2

end Lax263307Proofs.ComputedRounding
