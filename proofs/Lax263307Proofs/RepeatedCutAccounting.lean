import Lax263307.RepeatedCutAccounting
import Mathlib.Tactic

namespace Lax263307Proofs.RepeatedCutAccounting

open Lax263307.RepeatedCutAccounting

theorem disjoint_shore_card {n q : ℕ} (B : Fin q → Finset (Fin n))
    (disjoint : Pairwise fun i j => Disjoint (B i) (B j)) : (∑ i, (B i).card) ≤ n := by
  classical
  have hd : (↑(Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint B := by
    intro i _ j _ hij
    exact disjoint hij
  rw [← Finset.card_biUnion hd]
  simpa using Finset.card_le_univ (Finset.univ.biUnion B)

theorem cost_union_le_sum {n q : ℕ} (x : Fin n → ℝ) (nonnegative : ∀ v, 0 ≤ x v)
    (S : Fin q → Finset (Fin n)) : cost x (Finset.univ.biUnion S) ≤ ∑ i, cost x (S i) := by
  classical
  have hterm (v : Fin n) : (if v ∈ Finset.univ.biUnion S then x v else 0) ≤
      ∑ i, if v ∈ S i then x v else 0 := by
    by_cases h : v ∈ Finset.univ.biUnion S
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
      rw [if_pos h]
      have hs := Finset.single_le_sum (f := fun i => if v ∈ S i then x v else 0)
        (fun i _ => by split_ifs <;> first | exact nonnegative v | exact le_refl 0) (Finset.mem_univ i)
      simpa only [if_pos hi] using hs
    · rw [if_neg h]
      exact Finset.sum_nonneg fun i _ => by split_ifs <;> first | exact nonnegative v | exact le_refl 0
  calc
    _ = ∑ v : Fin n, if v ∈ Finset.univ.biUnion S then x v else 0 := by simp only [cost, Finset.sum_ite_mem, Finset.univ_inter]
    _ ≤ ∑ v : Fin n, ∑ i, if v ∈ S i then x v else 0 := Finset.sum_le_sum fun v _ => hterm v
    _ = ∑ i, ∑ v : Fin n, if v ∈ S i then x v else 0 := Finset.sum_comm
    _ = _ := by simp only [cost, Finset.sum_ite_mem, Finset.univ_inter]

/--
---
conclusion: Lax263307.RepeatedCutAccounting.total_cut_cost
---
The cost of a union is at most the sum of nonnegative individual costs.
Use the per-cut estimate and the original order bound on each left shore.
Pairwise disjoint discarded shores have total size at most n; summing
and factoring gives the claimed global cost bound.
-/
theorem total_cut_cost {n q : ℕ} (x : Fin n → ℝ) (nonnegative : ∀ v, 0 ≤ x v)
    (A B : Fin q → Finset (Fin n)) (disjoint : Pairwise fun i j => Disjoint (B i) (B j))
    (ρ γ : ℝ) (rho_nonnegative : 0 ≤ ρ) (gamma_positive : 0 < γ)
    (each_cut : ∀ i, cost x (A i ∩ B i) ≤ 4 * ρ * (A i).card * (B i).card / γ) :
    cost x (Finset.univ.biUnion fun i => A i ∩ B i) ≤ 4 * ρ * (n : ℝ) ^ 2 / γ := by
  classical
  have hcoef : 0 ≤ 4 * ρ * (n : ℝ) / γ := by positivity
  have hsum : (∑ i, ((B i).card : ℝ)) ≤ n := by exact_mod_cast disjoint_shore_card B disjoint
  have hA (i : Fin q) : ((A i).card : ℝ) ≤ n := by
    exact_mod_cast (show (A i).card ≤ n by simpa using Finset.card_le_univ (A i))
  calc
    _ ≤ ∑ i, cost x (A i ∩ B i) := cost_union_le_sum x nonnegative _
    _ ≤ ∑ i, (4 * ρ * (n : ℝ) / γ) * (B i).card := by
      apply Finset.sum_le_sum
      intro i _
      apply (each_cut i).trans
      have h := mul_le_mul_of_nonneg_left (hA i) (show 0 ≤ 4 * ρ * ((B i).card : ℝ) / γ by positivity)
      convert h using 1 <;> ring
    _ = (4 * ρ * (n : ℝ) / γ) * (∑ i, ((B i).card : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (4 * ρ * (n : ℝ) / γ) * n := mul_le_mul_of_nonneg_left hsum hcoef
    _ = _ := by ring


end Lax263307Proofs.RepeatedCutAccounting
