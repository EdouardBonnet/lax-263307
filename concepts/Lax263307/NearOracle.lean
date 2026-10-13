import Lax263307.ComputedSeparators
import Lax263307.ComputedRounding
import Lax263307.HeavyRationalConditioning
import Lax263307.AlgorithmParameters

/-!
---
title: Computed rounding oracle near the moment relaxation
type: theorem
---
The algorithm searches for a heavy conditioning set, computes separators
using the registered flow-cut solver, and queries the resulting parts.
Its actual output is either an independent set or a valid component cut
with a uniform gap and a bounded coefficient sum.

# Formalization notes

The child-query hypothesis is the induction hypothesis for the recursive
algorithm. All selections in the oracle are computable. Its implementation
and execution bounds in the registered RAM model are separate obligations.
-/

namespace Lax263307.NearOracle

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
    (y : RationalVector n (AlgorithmParameters.level a K B n D))
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))) : Result n :=
  let p := AlgorithmParameters.sparsity a K B n D
  match HeavyRationalConditioning.findHeavyConditioning G k p y with
  | none => .reject
  | some A =>
    let x := costs y A
    let cs := ComputedSeparators.cuts
      (ComputedSeparators.step flow G x B (AlgorithmParameters.load B n D) k) n Finset.univ
    let parts := ComputedSeparators.pieces cs
    let c : Option (Fin cs.length) → ℚ := fun i => ∑ v ∈ parts i, (x v : ℚ)
    match ComputedRounding.collect (order cs.length) parts (1 / D) k c
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
        ComponentCutEncoding.evaluate (ComponentCutEncoding.coefficient A C u) z ≤ 0) ∧
      η * (1 / (D : ℝ)) ^ 2 / (16 * n) ≤
        ComponentCutEncoding.evaluate (ComponentCutEncoding.coefficient A C u) x ∧
      (∑ T : Coordinate n r, |(ComponentCutEncoding.coefficient A C u T : ℝ)|) ≤ 2 * n
  | .reject => False

open GraphClasses PowerBagBounds AlgorithmParameters

axiom exists_oracle (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0 < a) (hA : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ (flow : List ℕ → List ℕ) (K B : ℕ), Lax759944.RamPolytime.RamPolytime flow ∧
      0 < K ∧ 0 < B ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (D k h : ℕ), 4 ≤ D → cutoff a K B n D < k →
      ∀ (y : RationalVector n (level a K B n D)),
      IsFeasible G k (level a K B n D) (realVector y) →
      ∀ (x : MomentVector n (level a K B n D)),
      (∀ T, |x T - realVector y T| ≤ (momentFloor a K B n D : ℝ) *
        (1 / (D : ℝ)) ^ 2 / (32 * (n : ℝ) ^ 2)) →
      ∀ (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))), ChildCorrect G D h child →
      Correct G k h D (momentFloor a K B n D) x (run flow a K B D G k y child)

end Lax263307.NearOracle
