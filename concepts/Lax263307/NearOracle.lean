import Lax263307.ComputedSeparators
import Lax263307.ComputedRounding
import Lax263307.HeavyRationalConditioning
import Lax263307.AlgorithmParameters

/-!
---
title: The recursive oracle near the moment relaxation
type: definition
---
The oracle searches for a heavy conditioning set, computes separators,
and queries the resulting parts. Its possible outputs are an independent
set, a component cut, or rejection.

The correctness predicate requires an approximation guarantee for a found
set and a valid inequality with a quantitative gap for a returned cut.
It rules out rejection under the oracle's hypotheses.

# Formalization notes

`ChildCorrect` specifies the recursive answers on balanced parts.
`Correct` specifies the corresponding answer or cut at the current level.
The function itself is computable for the supplied flow solver and child
queries.
-/

namespace Lax263307.NearOracle

open AlgorithmParameters (level load sparsity)
open ComponentCutEncoding (coefficient evaluate)
open ComputedRounding (collect)
open ComputedSeparators (cuts pieces step)
open HeavyRationalConditioning (findHeavyConditioning)
open scoped NNRat
open LinearRelaxation RationalConditioning

def costs {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) (v : Fin n) : ℚ≥0 :=
  ⟨max 0 (rationalValue y (insert v A) / rationalValue y A), le_max_left _ _⟩

def order (q : ℕ) : List (Option (Fin q)) := none :: (List.finRange q).map some

inductive Result (n : ℕ)
  | found (vertices : Finset (Fin n))
  | cut (conditioning vertices : Finset (Fin n)) (bound : ℕ)
  | reject

def run {n : ℕ} (flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ)
    (y : RationalVector n (level a K B n D))
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))) : Result n :=
  let p := sparsity a K B n D
  match findHeavyConditioning G k p y with
  | none => .reject
  | some A =>
    let x := costs y A
    let cs := cuts
      (step flow G x B (load B n D) k) n Finset.univ
    let parts := pieces cs
    let c : Option (Fin cs.length) → ℚ := fun i => ∑ v ∈ parts i, (x v : ℚ)
    match collect (order cs.length) parts (1 / D) k c
      (fun i t => child (parts i) t) with
    | .found I => .found I
    | .cut C u => .cut A C u

def ChildCorrect {n : ℕ} (G : SimpleGraph (Fin n)) (D h : ℕ)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))) : Prop :=
  ∀ C : Finset (Fin n), 3 * C.card ≤ 2 * n → ∀ t : ℕ,
    match child C t with
    | some I => I ⊆ C ∧ G.IsIndepSet (I : Set (Fin n)) ∧
        (1 - 4 * (1 / (D : ℝ))) ^ h * (t : ℝ) ≤ I.card
    | none => IsIndependenceBound G C (t - 1)

def Correct {n r : ℕ} (G : SimpleGraph (Fin n)) (k h D : ℕ) (η : ℝ)
    (x : MomentVector n r) : Result n → Prop
  | .found I => G.IsIndepSet (I : Set (Fin n)) ∧
      (1 - 4 * (1 / (D : ℝ))) ^ (h + 1) * (k : ℝ) ≤ I.card
  | .cut A C u => A.card ≤ r ∧ u ≤ n ∧ IsIndependenceBound G C u ∧
      (∀ z ∈ independentSetHull G k r,
        evaluate (coefficient A C u) z ≤ 0) ∧
      η * (1 / (D : ℝ)) ^ 2 / (16 * n) ≤
        evaluate (coefficient A C u) x ∧
      (∑ T : Coordinate n r, |(coefficient A C u T : ℝ)|) ≤ 2 * n
  | .reject => False

end Lax263307.NearOracle
