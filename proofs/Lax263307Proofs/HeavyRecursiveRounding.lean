import Lax263307.HeavyRecursiveRounding
import Lax263307.StrongComponentGaps
import Lax263307.ConditionedCosts
import Lax263307Proofs.RecursiveRounding
import Mathlib.Tactic

namespace Lax263307Proofs.HeavyRecursiveRounding

open Lax263307.LinearRelaxation Lax263307.SeparatorComponents
open Lax263307.ComponentCutEncoding

/--
---
conclusion: Lax263307.HeavyRecursiveRounding.ignored_cost
---
-/
theorem ignored_cost {n : ℕ} {ι : Type} [Fintype ι] (c : ι → ℝ) (δ k : ℝ)
    (hn : 0 < n) (hδ : 0 ≤ δ) (hk : 0 ≤ k) (count : Fintype.card ι ≤ 2 * n) :
    (∑ i, if δ * k / (4 * n) < c i then 0 else c i) ≤ δ * k / 2 := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcut : 0 ≤ δ * k / (4 * n) := by positivity
  have each (i : ι) : (if δ * k / (4 * n) < c i then 0 else c i) ≤ δ * k / (4 * n) := by
    split_ifs with h
    · exact hcut
    · exact not_lt.mp h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => each i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcount : (Fintype.card ι : ℝ) ≤ 2 * n := by exact_mod_cast count
  have heq : 2 * (n : ℝ) * (δ * k / (4 * n)) = δ * k / 2 := by field_simp; ring
  exact hsum.trans ((mul_le_mul_of_nonneg_right hcount hcut).trans_eq heq)

/--
---
conclusion: Lax263307.HeavyRecursiveRounding.heavy_union_size
---
-/
theorem heavy_union_size {n : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (P : Partition G S ι)
    (x : Fin n → ℝ) (k : ℕ) (h : ℕ) (δ : ℝ)
    (hn : 0 < n) (hδ : 0 ≤ δ) (small : δ ≤ 1 / 4)
    (count : Fintype.card ι ≤ 2 * n)
    (mass : (∑ v, x v) = k) (light : ∑ v ∈ S, x v ≤ δ * k)
    (I : ι → Finset (Fin n)) (targets : ι → ℕ)
    (inside : ∀ i, I i ⊆ P.vertices i)
    (independent : ∀ i, G.IsIndepSet (I i : Set (Fin n)))
    (rounded : ∀ i, δ * k / (4 * n) < ∑ v ∈ P.vertices i, x v →
      (1 - δ) * (∑ v ∈ P.vertices i, x v) < targets i)
    (answers : ∀ i, δ * k / (4 * n) < ∑ v ∈ P.vertices i, x v →
      (1 - 4 * δ) ^ h * (targets i : ℝ) ≤ (I i).card) :
    G.IsIndepSet (combine I : Set (Fin n)) ∧
      (1 - 4 * δ) ^ (h + 1) * (k : ℝ) ≤ (combine I).card := by
  classical
  let c (i : ι) := ∑ v ∈ P.vertices i, x v
  let cutoff : ℝ := δ * k / (4 * n)
  have hsplit : (∑ i, if cutoff < c i then c i else 0) +
      (∑ i, if cutoff < c i then 0 else c i) = ∑ i, c i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have hsum := Lax263307Proofs.RecursiveRounding.parts_sum P x
  have hignored := ignored_cost c δ k hn hδ (Nat.cast_nonneg k) count
  rw [mass] at hsum
  have hheavy : (1 - 3 * δ / 2) * (k : ℝ) ≤ ∑ i, if cutoff < c i then c i else 0 := by
    change (∑ i, c i) = _ at hsum
    change (∑ i, if cutoff < c i then 0 else c i) ≤ _ at hignored
    linarith
  have hf : 0 ≤ (1 - 4 * δ) ^ h := pow_nonneg (by linarith) _
  have hone : 0 ≤ 1 - δ := by linarith
  have each (i : ι) : (1 - 4 * δ) ^ h * (1 - δ) * (if cutoff < c i then c i else 0) ≤ (I i).card := by
    by_cases hi : cutoff < c i
    · rw [if_pos hi]
      have ht := (rounded i hi).le
      have ha := answers i hi
      have ht' : (1 - 4 * δ) ^ h * (1 - δ) * c i ≤ (1 - 4 * δ) ^ h * (targets i : ℝ) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht hf
      exact ht'.trans ha
    · rw [if_neg hi, mul_zero]
      exact Nat.cast_nonneg _
  obtain ⟨hI, hcard⟩ := Lax263307.RecursiveRounding.combine_independent G S P I inside independent
  have hanswers := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => each i)
  rw [← Finset.mul_sum] at hanswers
  have hmass := mul_le_mul_of_nonneg_left hheavy (mul_nonneg hf hone)
  have hstep : 1 - 4 * δ ≤ (1 - δ) * (1 - 3 * δ / 2) := by nlinarith [sq_nonneg δ]
  have hstep' := mul_le_mul_of_nonneg_right hstep (mul_nonneg hf (Nat.cast_nonneg k))
  have hfinal : (1 - 4 * δ) ^ (h + 1) * (k : ℝ) ≤ ∑ i, ((I i).card : ℝ) := by
    rw [pow_succ]
    nlinarith [hanswers, hmass, hstep']
  exact ⟨hI, hfinal.trans_eq (by exact_mod_cast hcard.symm)⟩




/--
---
conclusion: Lax263307.HeavyRecursiveRounding.strong_round_or_cut
---
-/
theorem strong_round_or_cut {n r : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (k h : ℕ) (δ η : ℝ)
    (hn : 0 < n) (hk : 0 < k) (hδ : 0 < δ) (small : δ ≤ 1 / 4) (hη : 0 < η)
    (x y : MomentVector n r) (feasible : Lax263307.LinearRelaxation.IsFeasible G k r y)
    (A S : Finset (Fin n)) (P : Partition G S ι) (size : A.card ≤ r)
    (moment : η ≤ value y A) (count : Fintype.card ι ≤ 2 * n)
    (light : ∑ v ∈ S, conditioned y A v ≤ δ * k)
    (I : ι → Finset (Fin n)) (targets : ι → ℕ)
    (inside : ∀ i, I i ⊆ P.vertices i)
    (independent : ∀ i, G.IsIndepSet (I i : Set (Fin n)))
    (target_lower : ∀ i, δ * k / (4 * n) < ∑ v ∈ P.vertices i, conditioned y A v →
      (1 - δ) * (∑ v ∈ P.vertices i, conditioned y A v) < targets i)
    (target_upper : ∀ i, δ * k / (4 * n) < ∑ v ∈ P.vertices i, conditioned y A v →
      (targets i - 1 : ℕ) ≤ (1 - δ) * (∑ v ∈ P.vertices i, conditioned y A v))
    (queries : ∀ i, δ * k / (4 * n) < ∑ v ∈ P.vertices i, conditioned y A v →
      ((1 - 4 * δ) ^ h * (targets i : ℝ) ≤ (I i).card) ∨
        IsIndependenceBound G (P.vertices i) (targets i - 1))
    (near : ∀ B, |x B - y B| ≤ η * δ ^ 2 / (32 * (n : ℝ) ^ 2)) :
    (G.IsIndepSet (combine I : Set (Fin n)) ∧
      (1 - 4 * δ) ^ (h + 1) * (k : ℝ) ≤ (combine I).card) ∨
      ∃ i, (∀ z ∈ independentSetHull G k r,
        evaluate (coefficient A (P.vertices i) (targets i - 1)) z ≤ 0) ∧
        η * δ ^ 2 / (16 * n) ≤ evaluate (coefficient A (P.vertices i) (targets i - 1)) x := by
  classical
  have hpos : 0 < value y A := hη.trans_le moment
  have hinv := Lax263307.ConditionedCosts.conditioning_invariants G k r y feasible A size hpos
  by_cases hfail : ∃ i, δ * k / (4 * n) < ∑ v ∈ P.vertices i, conditioned y A v ∧
      IsIndependenceBound G (P.vertices i) (targets i - 1)
  · obtain ⟨i, hactive, hbound⟩ := hfail
    have hcost0 : 0 ≤ ∑ v ∈ P.vertices i, conditioned y A v :=
      Finset.sum_nonneg (fun v _ => (hinv.1 v).1)
    have hcost1 : (∑ v ∈ P.vertices i, conditioned y A v) ≤ (P.vertices i).card := by
      simpa using Finset.sum_le_sum (fun v (_ : v ∈ P.vertices i) => (hinv.1 v).2)
    have hcard : (P.vertices i).card ≤ n := (P.vertices i).card_le_univ.trans_eq (Fintype.card_fin n)
    have hupper : targets i - 1 ≤ n := by
      have h := target_upper i hactive
      have hc : ((P.vertices i).card : ℝ) ≤ n := by exact_mod_cast hcard
      have hu : (targets i - 1 : ℕ) ≤ (n : ℝ) := by nlinarith
      exact_mod_cast hu
    have hheavy : (δ / 2) * (k : ℝ) / (2 * n) ≤ ∑ v ∈ P.vertices i, conditioned y A v := by
      convert hactive.le using 1 <;> first | rfl | ring
    have hround : (targets i - 1 : ℕ) ≤ (1 - δ / 2) * ∑ v ∈ P.vertices i, conditioned y A v := by
      nlinarith [target_upper i hactive]
    have hnear : ∀ B, |x B - y B| ≤ η * (δ / 2) ^ 2 / (8 * (n : ℝ) ^ 2) := by
      intro B
      convert near B using 1; ring
    obtain ⟨hvalid, hgap⟩ := Lax263307.StrongComponentGaps.query_gap G k x y A (P.vertices i)
      (targets i - 1) size hbound hupper η (δ / 2) hη (by linarith) hn hk moment hheavy hround hnear
    right
    refine ⟨i, hvalid, ?_⟩
    convert hgap using 1; ring
  · left
    apply heavy_union_size G S P (conditioned y A) k h δ hn hδ.le small count hinv.2.1 light I targets
      inside independent target_lower
    intro i hi
    exact (queries i hi).resolve_right (fun hb => hfail ⟨i, hi, hb⟩)

end Lax263307Proofs.HeavyRecursiveRounding
