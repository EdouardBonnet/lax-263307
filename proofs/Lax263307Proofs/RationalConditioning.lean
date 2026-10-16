import Lax263307.RationalConditioning
import Lax263307Proofs.EntropyDecrease
import Mathlib.Data.Nat.Choose.Bounds

namespace Lax263307Proofs.RationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning
open EntropyDecrease

theorem value_cast {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) :
    value (realVector y) A = (rationalValue y A : ℝ) := by
  by_cases hA : A.card ≤ r + 2 <;> simp [value, realVector, rationalValue, hA]

theorem edge_cost_formula {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) (hA : 0 < rationalValue y A) :
    edgeCost G (conditioned (realVector y) A) =
      (edgeNumerator G y A : ℝ) / (2 * (rationalValue y A : ℝ) ^ 2) := by
  have hpos : (0 : ℝ) < (rationalValue y A : ℝ) := by exact_mod_cast hA
  have hcost : conditioned (realVector y) A = fun v =>
      (rationalValue y (insert v A) : ℝ) / (rationalValue y A : ℝ) := by
    funext v
    simp [conditioned, value_cast]
  have hnum : adjacencyMass G (fun v => (rationalValue y (insert v A) : ℝ)) =
      (edgeNumerator G y A : ℝ) := by
    unfold adjacencyMass edgeNumerator
    push_cast
    simp only [apply_ite, Rat.cast_mul, Rat.cast_zero]
  rw [edgeCost, hcost, adjacencyMass_div G _ _ (ne_of_gt hpos), hnum]
  ring

theorem passes_iff {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) (hp : 0 < p) :
    Passes G k p y A ↔ 0 < value (realVector y) A ∧
      edgeCost G (conditioned (realVector y) A) ≤ (k : ℝ) ^ 2 / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  constructor
  · rintro ⟨hpos, hineq⟩
    have hposR : (0 : ℝ) < (rationalValue y A : ℝ) := by exact_mod_cast hpos
    refine ⟨by rw [value_cast]; exact hposR, ?_⟩
    rw [edge_cost_formula G y A hpos]
    apply (div_le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hposR)) hpR).2
    have hR : (p : ℝ) * (edgeNumerator G y A : ℝ) ≤
        2 * (k : ℝ) ^ 2 * (rationalValue y A : ℝ) ^ 2 := by exact_mod_cast hineq
    nlinarith
  · rintro ⟨hposR, hineq⟩
    rw [value_cast] at hposR
    have hpos : 0 < rationalValue y A := by exact_mod_cast hposR
    refine ⟨hpos, ?_⟩
    rw [edge_cost_formula G y A hpos] at hineq
    have hR := (div_le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hposR)) hpR).1 hineq
    have hresult : (p : ℝ) * (edgeNumerator G y A : ℝ) ≤
        2 * (k : ℝ) ^ 2 * (rationalValue y A : ℝ) ^ 2 := by nlinarith
    exact_mod_cast hresult

/--
---
conclusion: Lax263307.RationalConditioning.candidate_complete
---
The fixed-order enumeration contains exactly the sets within the budget.

# Proof strategy

A sublist of the vertex list has no duplicates, so its length equals the
cardinality of its vertex set. Conversely, filter the vertex list by any
given set and select that sublist at its cardinality.
-/
theorem candidate_complete (n r : ℕ) (A : Finset (Fin n)) :
    A ∈ candidates n r ↔ A.card ≤ r := by
  constructor
  · intro h
    obtain ⟨j, hj, hm⟩ := List.mem_flatMap.mp h
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
    have hsub := (List.mem_sublistsLen.mp hl).1
    have hlen := (List.mem_sublistsLen.mp hl).2
    have hnd := hsub.nodup (List.nodup_finRange n)
    rw [List.toFinset_card_of_nodup hnd, hlen]
    have := List.mem_range.mp hj
    omega
  · intro hA
    let l := (List.finRange n).filter fun v => decide (v ∈ A)
    have hsub : List.Sublist l (List.finRange n) := List.filter_sublist
    have hnd : l.Nodup := hsub.nodup (List.nodup_finRange n)
    have heq : l.toFinset = A := by ext v; simp [l]
    have hlen : l.length = A.card := by rw [← List.toFinset_card_of_nodup hnd, heq]
    apply List.mem_flatMap.mpr
    refine ⟨A.card, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    exact ⟨l, List.mem_sublistsLen.mpr ⟨hsub, hlen⟩, heq⟩

theorem candidate_count (n r : ℕ) :
    (candidates n r).length = ∑ j ∈ Finset.range (r + 1), n.choose j := by
  induction r with
  | zero => simp [candidates, List.sublistsLen_zero]
  | succ r ih =>
    have hrec : (candidates n (r + 1)).length =
        (candidates n r).length + n.choose (r + 1) := by
      simp [candidates, List.range_succ, List.flatMap_append, List.length_sublistsLen, Nat.add_assoc]
    calc
      (candidates n (r + 1)).length =
          (∑ j ∈ Finset.range (r + 1), n.choose j) + n.choose (r + 1) := by rw [hrec, ih]
      _ = ∑ j ∈ Finset.range (r + 1 + 1), n.choose j :=
        (Finset.sum_range_succ (fun j => n.choose j) (r + 1)).symm

/--
---
conclusion: Lax263307.RationalConditioning.candidate_bound
---
The enumeration contains at most `(r+1)(n+1)^r` candidates.

# Proof strategy

The exact count is the sum of binomial coefficients for sizes zero through
`r`. Bound each coefficient by a power of the order, then by `(n+1)^r`.
-/
theorem candidate_bound (n r : ℕ) : (candidates n r).length ≤ (r + 1) * (n + 1) ^ r := by
  rw [candidate_count]
  calc
    (∑ j ∈ Finset.range (r + 1), n.choose j) ≤
        ∑ _j ∈ Finset.range (r + 1), (n + 1) ^ r := by
      apply Finset.sum_le_sum
      intro j hj
      have hjr : j ≤ r := by have := Finset.mem_range.mp hj; omega
      calc
        n.choose j ≤ n ^ j := Nat.choose_le_pow n j
        _ ≤ (n + 1) ^ r := by gcongr <;> omega
    _ = _ := by simp


end Lax263307Proofs.RationalConditioning
