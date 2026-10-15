import Lax263307.RecursiveAlgorithm
import Lax263307.BlowUpBagBounds
import Lax263307.PositiveWeights
import Lax263307.WeightedProjection
import Mathlib.Algebra.BigOperators.Fin

/-!
---
title: The weighted independent-set approximation algorithm
type: definition
---
Clip negative weights, round the remaining weights to copy multiplicities,
and run the unweighted algorithm on the independent blow-up. Project the
answer back to the original vertices and discard nonpositive-weight
vertices. Empty and nonpositive instances return the empty set.

# Formalization notes

The function takes fixed LP and flow solvers as arguments. Blow-up vertices
are numbered by the finite-sigma equivalence. The complete correctness,
RAM execution, and running-time guarantees are supplied by the proof of
the main QPTAS theorem.
-/

namespace Lax263307.WeightedAlgorithm

open RecursiveAlgorithm (independentSet)
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
    let I := independentSet lp flow a K B (numbered G copies') (ε/2)
    discardNonpositive w (project (I.image (labeling copies')))

end Lax263307.WeightedAlgorithm
