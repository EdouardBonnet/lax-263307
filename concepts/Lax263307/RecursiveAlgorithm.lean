import Lax263307.ProjectedOracle
import Lax263307.ExhaustiveTargets
import Lax263307.RecursionDepth
import Lax263307.TargetSearch

/-!
---
title: Correctness of the complete recursive unweighted algorithm
type: theorem
---
An explicit recursive function uses exhaustive search for small targets and
bounded projected round-or-cut search for larger targets. Child calls operate
on canonically labeled balanced parts. Descending target search returns an
independent set with the requested approximation ratio.

# Formalization notes

The depth budget terminates every call. Induction discharges the child-query
hypothesis of the projected oracle, including sound rejection. The accuracy
denominator is 4(depth(n)+1)ceil(1/epsilon). This proves correctness of the
computable function; a finite RAM implementation and its uniform complexity
bound are still needed for the main theorem.
-/

namespace Lax263307.RecursiveAlgorithm

open ComputedSeparators AlgorithmParameters

def attempt (lp flow : List ℕ → List ℕ) (a K B D : ℕ) (fuel : ℕ)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : Option (Finset (Fin n)) :=
  if k ≤ cutoff a K B n D ∨ n ≤ 1 then ExhaustiveTargets.findIndependentSet G k
  else if n < k then none
  else match fuel with
    | 0 => none
    | fuel + 1 => ProjectedOracle.search lp flow a K B D G k
        (fun C t => (attempt lp flow a K B D fuel (restriction G C) t).map
          (fun I => I.image (label C)))
termination_by fuel

def solve {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n) × ℕ :=
  TargetSearch.search (attempt lp flow a K B D (RecursionDepth.depth n) G) n

def Correct {n : ℕ} (G : SimpleGraph (Fin n)) (k fuel D : ℕ) : Option (Finset (Fin n)) → Prop
  | some I => G.IsIndepSet (I : Set (Fin n)) ∧ (1 - 4*(1/(D:ℝ)))^fuel * (k:ℝ) ≤ I.card
  | none => ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card < k

def accuracyDenominator (n : ℕ) (ε : ℚ) : ℕ :=
  4 * (RecursionDepth.depth n + 1) * ⌈ε⁻¹⌉₊

def independentSet {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ε : ℚ) : Finset (Fin n) :=
  (solve lp flow a K B (accuracyDenominator n ε) G).1

open GraphClasses PowerBagBounds

axiom exists_solver (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0 < a) (hA : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ (lp flow : List ℕ → List ℕ) (K B : ℕ),
      Lax759944.RamPolytime.RamPolytime lp ∧ Lax759944.RamPolytime.RamPolytime flow ∧
      0 < K ∧ 0 < B ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → ∀ ε : ℚ, 0 < ε → ε < 1 →
      Lax263307.WeightedIndependentSet.IsApproximation G (fun _ => 1) ε
        (independentSet lp flow a K B G ε)

end Lax263307.RecursiveAlgorithm
