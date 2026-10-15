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
  have hignored := Lax263307.HeavyRecursiveRounding.ignored_cost c δ k hn hδ (Nat.cast_nonneg k) count
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


end Lax263307Proofs.HeavyRecursiveRounding
