import Lax263307.ProjectedOracle
import Lax263307.ExhaustiveTargets
import Lax263307.RecursionDepth
import Lax263307.TargetSearch

/-!
---
title: The recursive unweighted approximation algorithm
type: definition
---
The algorithm uses exhaustive search for small targets and projected
round-or-cut search for larger targets. Recursive calls work on canonically
labeled balanced parts. A descending target search selects the final set.

# Formalization notes

The fuel parameter bounds recursion depth. `Correct` records the size
guarantee for a returned independent set and the upper bound certified by
failure. The accuracy denominator is
$4(\operatorname{depth}(n)+1)\lceil1/\varepsilon\rceil$.
-/

namespace Lax263307.RecursiveAlgorithm

open ExhaustiveTargets (findIndependentSet)
open RecursionDepth (depth)
open ComputedSeparators AlgorithmParameters

def attempt (lp flow : List ℕ → List ℕ) (a K B D : ℕ) (fuel : ℕ)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : Option (Finset (Fin n)) :=
  if k ≤ cutoff a K B n D ∨ n ≤ 1 then findIndependentSet G k
  else if n < k then none
  else match fuel with
    | 0 => none
    | fuel + 1 => ProjectedOracle.search lp flow a K B D G k
        (fun C t => (attempt lp flow a K B D fuel (restriction G C) t).map
          (fun I => I.image (label C)))
termination_by fuel

def solve {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Finset (Fin n) × ℕ :=
  TargetSearch.search (attempt lp flow a K B D (depth n) G) n

def Correct {n : ℕ} (G : SimpleGraph (Fin n)) (k fuel D : ℕ) : Option (Finset (Fin n)) → Prop
  | some I => G.IsIndepSet (I : Set (Fin n)) ∧ (1 - 4*(1/(D:ℝ)))^fuel * (k:ℝ) ≤ I.card
  | none => ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card < k

def accuracyDenominator (n : ℕ) (ε : ℚ) : ℕ :=
  4 * (depth n + 1) * ⌈ε⁻¹⌉₊

def independentSet {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ε : ℚ) : Finset (Fin n) :=
  (solve lp flow a K B (accuracyDenominator n ε) G).1

end Lax263307.RecursiveAlgorithm
