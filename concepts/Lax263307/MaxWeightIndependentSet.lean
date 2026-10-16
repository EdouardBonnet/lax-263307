import Lax263307.GraphClasses
import Lax263307.WeightedIndependentSet
import Lax213208.QPTAS
import Lax560851.StructuralCombinators

/-!
---
title: Maximum-weight independent set as an optimization problem
type: definition
---
We use the optimization-problem and approximation-scheme definitions of
lax-213208. An instance is the canonical packet containing the graph order,
its row-major adjacency matrix, and the rational vertex weights. The packet
uses the registered structural presentation of a list of natural numbers.
For precision $k>0$, the scheme receives the structural arena of $(k,x)$.

A feasible output is a zero-one membership vector of an independent set.
The objective is its total weight, with negative totals replaced by zero
to meet the archive's nonnegative-objective convention. This does not change
the optimum: the empty set is feasible and has value zero. The approximation
proof also establishes that the returned set has nonnegative total weight.

The input class consists exactly of canonical packets of graphs in
$\mathcal C$, with arbitrary rational weights. No solution, separator, or
other computed advice is included in the input presentation.
-/

namespace Lax263307

open GraphClasses WeightedIndependentSet
open Lax213208.OptimizationProblem
open Lax560851.StructuralPresentation Lax560851.StructuralCombinators

namespace MaxWeightIndependentSet

open scoped Classical in
/-- Graph and weights, without the separately supplied accuracy parameter. -/
noncomputable abbrev encodeInstance {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Fin n → ℚ) : List ℕ :=
  [n] ++ (List.ofFn fun u => List.ofFn fun v =>
    if G.Adj u v then 1 else 0).flatten ++
    (List.ofFn w).flatMap encodeRational

/-- Number of vertices recorded in the instance packet. -/
abbrev vertexCount (input : List ℕ) : ℕ := input.headD 0

/-- Decode the adjacency matrix as a symmetric, loopless graph. -/
def decodeGraph (input : List ℕ) : SimpleGraph (Fin (vertexCount input)) where
  Adj u v := u ≠ v ∧ input.getD (1 + u.val * vertexCount input + v.val) 0 ≠ 0 ∧
    input.getD (1 + v.val * vertexCount input + u.val) 0 ≠ 0
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (input : List ℕ) : DecidableRel (decodeGraph input).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ _ ≠ 0 ∧ _ ≠ 0))

/-- Decode the rational weight following the adjacency matrix. -/
def decodeWeights (input : List ℕ) (v : Fin (vertexCount input)) : ℚ :=
  let offset := 1 + vertexCount input * vertexCount input + 3 * v.val
  let numerator : ℚ := input.getD (offset + 1) 0
  let denominator : ℚ := input.getD (offset + 2) 0
  (if input.getD offset 0 = 0 then numerator else -numerator) / denominator

/-- Vertices marked by the output membership vector. -/
def decodeSolution (input output : List ℕ) : Finset (Fin (vertexCount input)) :=
  Finset.univ.filter fun v => output.getD v.val 0 = 1

/-- A feasible output is a zero-one vector representing an independent set. -/
def IsFeasible (input output : List ℕ) : Prop :=
  output.length = vertexCount input ∧ (∀ b ∈ output, b = 0 ∨ b = 1) ∧
    (decodeGraph input).IsIndepSet (decodeSolution input output : Set (Fin (vertexCount input)))

/-- Nonnegative objective required by the registered optimization framework. -/
def objectiveValue (input output : List ℕ) : NNReal :=
  Real.toNNReal (weight (decodeWeights input) (decodeSolution input output))

/-- Canonical graph-and-weight instances for a graph class. -/
def instancesOn (C : GraphClass) : Set (List ℕ) :=
  {input | ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → ℚ),
    G ∈ C n ∧ input = encodeInstance G w}

/-- Constructor injectivity certifies the structural list encoding. -/
private theorem inputEncoding_injective :
    ∀ (xs ys : List ℕ), listToRaw nat xs = listToRaw nat ys → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: xs, _ :: ys, h =>
      let equalFields := Lax560851.StructuralPresentation.Raw.pair.inj h
      congrArg₂ List.cons (Lax560851.StructuralPresentation.Raw.nat.inj equalFields.1)
        (inputEncoding_injective xs ys equalFields.2)

end MaxWeightIndependentSet

/-- Maximum-weight independent set with canonical structural input and membership-vector output. -/
def MaxWeightIndependentSet : Problem (List ℕ) (List ℕ) where
  direction := .maximize
  feasible := MaxWeightIndependentSet.IsFeasible
  value := MaxWeightIndependentSet.objectiveValue
  input := list nat
  output := id
  input_faithful := fun {xs ys} => MaxWeightIndependentSet.inputEncoding_injective xs ys
  output_injective := Function.injective_id

end Lax263307
