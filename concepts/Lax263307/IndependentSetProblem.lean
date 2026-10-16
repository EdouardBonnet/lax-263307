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
the optimum: the empty set is feasible and has value zero. The program
constructed below returns a set of nonnegative total weight.

The input class consists exactly of canonical packets of graphs in
$\mathcal C$, with arbitrary rational weights. No solution, separator, or
other computed advice is included in the input presentation.
-/

namespace Lax263307.IndependentSetProblem

open GraphClasses WeightedIndependentSet
open Lax213208.OptimizationProblem
open Lax560851.StructuralPresentation Lax560851.StructuralCombinators

/-- Graph and weights, without the separately supplied accuracy parameter. -/
noncomputable abbrev encodeInstance {n : ℕ} (G : SimpleGraph (Fin n))
    (w : Fin n → ℚ) : List ℕ := by
  classical
  exact [n] ++ (List.ofFn fun u => List.ofFn fun v =>
    if G.Adj u v then 1 else 0).flatten ++
    (List.ofFn w).flatMap encodeRational

abbrev order (x : List ℕ) : ℕ := x.headD 0

/-- Interpret the matrix; symmetry and the absent diagonal are explicit. -/
def graph (x : List ℕ) : SimpleGraph (Fin (order x)) where
  Adj u v := u ≠ v ∧ x.getD (1 + u.val * order x + v.val) 0 ≠ 0 ∧
    x.getD (1 + v.val * order x + u.val) 0 ≠ 0
  symm := ⟨by rintro u v ⟨hne, huv, hvu⟩; exact ⟨Ne.symm hne, hvu, huv⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance (x : List ℕ) : DecidableRel (graph x).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ _ ≠ 0 ∧ _ ≠ 0))

def weights (x : List ℕ) (v : Fin (order x)) : ℚ :=
  let offset := 1 + order x * order x + 3 * v.val
  let numerator : ℚ := x.getD (offset + 1) 0
  let denominator : ℚ := x.getD (offset + 2) 0
  (if x.getD offset 0 = 0 then numerator else -numerator) / denominator

def selected (x y : List ℕ) : Finset (Fin (order x)) :=
  Finset.univ.filter fun v => y.getD v.val 0 = 1

def feasible (x y : List ℕ) : Prop :=
  y.length = order x ∧ (∀ b ∈ y, b = 0 ∨ b = 1) ∧
    (graph x).IsIndepSet (selected x y : Set (Fin (order x)))

def value (x y : List ℕ) : NNReal :=
  Real.toNNReal (weight (weights x) (selected x y))

/-- The standard structural-list presentation is injective by its constructors.
This proof is axiom-free so it can be used inside a concept definition. -/
private theorem input_faithful : (list nat).Faithful := by
  intro x y h
  change listToRaw nat x = listToRaw nat y at h
  induction x generalizing y with
  | nil => cases y <;> cases h; rfl
  | cons x xs ih =>
    cases y with
    | nil => cases h
    | cons y ys =>
      change Lax560851.StructuralPresentation.Raw.pair (.nat x) (listToRaw nat xs) =
        Lax560851.StructuralPresentation.Raw.pair (.nat y) (listToRaw nat ys) at h
      obtain ⟨hx, ht⟩ := Lax560851.StructuralPresentation.Raw.pair.inj h
      exact congrArg₂ List.cons (Lax560851.StructuralPresentation.Raw.nat.inj hx) (ih ht)

def problem : Problem (List ℕ) (List ℕ) where
  direction := .maximize
  feasible := feasible
  value := value
  input := list nat
  output := id
  input_faithful := input_faithful
  output_injective := fun _ _ h => h

def instances (C : GraphClass) : Set (List ℕ) :=
  {x | ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → ℚ),
    G ∈ C n ∧ x = encodeInstance G w}

end Lax263307.IndependentSetProblem
