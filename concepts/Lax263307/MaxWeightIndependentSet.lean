import Lax263307.GraphClasses
import Lax263307.IndependentSetEncoding
import Lax213208.OptimizationProblem

/-!
---
title: Maximum-weight independent set as an optimization problem
type: definition
---
An instance is a finite simple graph with rational vertex weights. A feasible
solution is an independent vertex set in that graph. Its objective is the
nonnegative part of its total weight, as required by lax-213208. This does not
change the optimum: the empty set is feasible and has weight zero.
The approximation proof also ensures that the returned set has nonnegative
weight.

Membership in the input class means precisely that the instance graph belongs
to $\mathcal C$; all rational weight assignments are allowed. The separate
`IndependentSetEncoding` concept fixes the standard representations used to
measure running time. Feasibility, objective values, and class membership are
defined directly on mathematical objects, without decoding machine words.
-/

namespace Lax263307

open GraphClasses WeightedIndependentSet
open Lax213208.OptimizationProblem

namespace MaxWeightIndependentSet

/-- A feasible solution is an independent set of the instance graph. -/
def IsFeasible (x : Instance) (s : Solution) : Prop :=
  ∃ I : Finset (Fin x.order), s = ⟨x.order, I⟩ ∧
    x.graph.IsIndepSet (I : Set (Fin x.order))

/-- Total weight, clipped at zero to meet the nonnegative-objective convention. -/
def objectiveValue (x : Instance) (s : Solution) : NNReal :=
  if h : s.1 = x.order then
    Real.toNNReal (weight x.weights (h ▸ s.2))
  else 0

/-- Weighted graphs whose underlying graph belongs to the given class. -/
def instancesOn (C : GraphClass) : Set Instance :=
  {x | x.graph ∈ C x.order}

end MaxWeightIndependentSet

/-- The mathematical optimization problem with its fixed canonical representations. -/
noncomputable def MaxWeightIndependentSet : Problem Instance Solution where
  direction := .maximize
  feasible := MaxWeightIndependentSet.IsFeasible
  value := MaxWeightIndependentSet.objectiveValue
  input := IndependentSetEncoding.input
  output := IndependentSetEncoding.output
  input_faithful := IndependentSetEncoding.input_faithful
  output_injective := IndependentSetEncoding.output_injective

end Lax263307
