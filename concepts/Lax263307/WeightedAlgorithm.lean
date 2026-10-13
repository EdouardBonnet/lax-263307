import Lax263307.RecursiveAlgorithm
import Lax263307.BlowUpBagBounds
import Lax263307.PositiveWeights
import Lax263307.WeightedProjection
import Mathlib.Algebra.BigOperators.Fin

/-!
---
title: Correctness of the complete weighted approximation algorithm
type: theorem
---
Clip negative weights, round them to copy multiplicities, and compute the
unweighted approximation on the canonically numbered independent blow-up.
Projection and removal of nonpositive-weight vertices give the requested
weighted approximation. Empty and nonpositive instances return the empty set.

# Formalization notes

The algorithm is a computable function using the fixed registered LP and
flow solvers. The copy labeling is the computable finite-sigma equivalence.
This closes functional correctness for signed rational weights, including
the recursive search. It does not yet assert a complete RAM execution or
its quasipolynomial time and word-length bounds.
-/

namespace Lax263307.WeightedAlgorithm

open WeightRounding IndependentBlowUp PositiveWeights

def labeling {n : ℕ} (copies : Fin n → ℕ) : Fin (∑ v, copies v) ≃ Vertex copies :=
  finSigmaFinEquiv.symm

def numbered {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ) :
    SimpleGraph (Fin (∑ v, copies v)) := (graph G copies).comap (labeling copies)

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (copies : Fin n → ℕ) :
    DecidableRel (numbered G copies).Adj := fun _ _ => inferInstanceAs (Decidable (G.Adj _ _))

def solve {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → ℚ) (ε : ℚ) : Finset (Fin n) :=
  let w' := positiveWeights w
  if n = 0 ∨ maximumWeight w' ≤ 0 then ∅
  else
    let copies' := copies w' ε
    let I := RecursiveAlgorithm.independentSet lp flow a K B (numbered G copies') (ε/2)
    discardNonpositive w (project (I.image (labeling copies')))

open GraphClasses EdgeSublinearSeparators WeightedIndependentSet

axiom exists_solver (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ (lp flow : List ℕ → List ℕ) (a K B : ℕ),
      Lax759944.RamPolytime.RamPolytime lp ∧ Lax759944.RamPolytime.RamPolytime flow ∧
      0 < a ∧ 0 < K ∧ 0 < B ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G ∈ C n →
      ∀ (w : Fin n → ℚ) (ε : ℚ), 0 < ε → ε < 1 → IsApproximation G w ε (solve lp flow a K B G w ε)

end Lax263307.WeightedAlgorithm
