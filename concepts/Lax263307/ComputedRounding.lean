import Lax263307.HeavyRecursiveRounding
import Mathlib.Data.Rat.Floor

/-!
---
title: Computing the recursive answer-or-cut decision
type: lemma
---
Round each part's rational cost to a target. Skip queries on light parts.
Scan child answers in a fixed order: the first failed query determines the
returned component inequality; if all required queries succeed, return the
union of their independent sets. The selected inequality has the required
positive gap and coefficient bound, and the returned union has the required
approximation guarantee.

# Formalization notes

The decision and target formulas are computable. Child-query correctness is
an explicit induction hypothesis for this one recursive step. This does not
assert correctness or a RAM bound for the complete recursive program.
-/

namespace Lax263307.ComputedRounding

open SeparatorComponents (combine)

def target (δ cost : ℚ) : ℕ := ⌊(1 - δ) * cost⌋₊ + 1

def answer {n : ℕ} {ι : Type} (δ : ℚ) (k : ℕ) (cost : ι → ℚ)
    (query : ι → ℕ → Option (Finset (Fin n))) (i : ι) : Option (Finset (Fin n)) :=
  if δ * k / (4 * n) < cost i then query i (target δ (cost i)) else some ∅

inductive Result (n : ℕ)
  | found (vertices : Finset (Fin n))
  | cut (vertices : Finset (Fin n)) (bound : ℕ)

def collect {n : ℕ} {ι : Type} [Fintype ι] (order : List ι) (parts : ι → Finset (Fin n))
    (δ : ℚ) (k : ℕ) (cost : ι → ℚ) (query : ι → ℕ → Option (Finset (Fin n))) : Result n :=
  match order.find? (fun i => (answer δ k cost query i).isNone) with
  | some i => .cut (parts i) (target δ (cost i) - 1)
  | none => .found (combine (fun i => (answer δ k cost query i).getD ∅))

open LinearRelaxation SeparatorComponents
open ComponentCutEncoding

axiom collect_correct {n r : ℕ} {ι : Type} [Fintype ι]
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
        (∑ B : Coordinate n r, |(coefficient A C u B : ℝ)|) ≤ 2 * n

end Lax263307.ComputedRounding
