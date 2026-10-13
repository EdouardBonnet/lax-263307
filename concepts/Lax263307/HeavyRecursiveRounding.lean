import Lax263307.StrongComponentGaps
import Lax263307.ConditionedCosts
import Lax263307.RecursiveRounding

/-!
---
title: Recursive rounding after discarding light parts
type: theorem
---
At most 2n parts whose conditioned cost is at most delta*k/(4n) lose
at most delta*k/2 in total. Approximate answers at rounded targets on
all heavier parts combine into an independent set, losing a factor
at most 1-4delta per recursive level. A failed heavy query instead gives
a valid component inequality with a uniform positive gap at the nearby
queried moment vector.

# Formalization notes

These are the mathematical answer-or-cut invariants for the recursive
oracle. They do not assume that every part receives a recursive query.
The explicit RAM loop and its running time remain separate obligations.
-/

namespace Lax263307.HeavyRecursiveRounding

open Lax263307.LinearRelaxation Lax263307.SeparatorComponents
open Lax263307.ComponentCutEncoding

axiom ignored_cost {n : ℕ} {ι : Type} [Fintype ι] (c : ι → ℝ) (δ k : ℝ)
    (hn : 0 < n) (hδ : 0 ≤ δ) (hk : 0 ≤ k) (count : Fintype.card ι ≤ 2 * n) :
    (∑ i, if δ * k / (4 * n) < c i then 0 else c i) ≤ δ * k / 2

axiom heavy_union_size {n : ℕ} {ι : Type} [Fintype ι]
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
      (1 - 4 * δ) ^ (h + 1) * (k : ℝ) ≤ (combine I).card

axiom strong_round_or_cut {n r : ℕ} {ι : Type} [Fintype ι]
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
        η * δ ^ 2 / (16 * n) ≤ evaluate (coefficient A (P.vertices i) (targets i - 1)) x

end Lax263307.HeavyRecursiveRounding
