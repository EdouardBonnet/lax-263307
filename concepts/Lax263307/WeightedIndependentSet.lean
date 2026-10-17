import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Floor

/-!
---
title: Weighted independent sets
type: definition
---
An instance consists of a finite simple graph and rational vertex weights.
A solution is a vertex set together with its ambient number of vertices.
The ambient number allows solutions for graphs of different orders to share
one type; feasibility requires it to agree with the instance.

An $(1-\varepsilon)$-approximation has weight at least
$(1-\varepsilon)w(J)$ for every independent set $J$.
Weights may be negative, and the empty set is always feasible.
All definitions here concern mathematical objects, independently of their
machine representations.
-/

namespace Lax263307.WeightedIndependentSet

/-- A finite graph with rational vertex weights. -/
structure Instance where
  order : ℕ
  graph : SimpleGraph (Fin order)
  weights : Fin order → ℚ

/-- A vertex set in an explicitly specified finite ambient set. -/
abbrev Solution := (n : ℕ) × Finset (Fin n)

/-- Total weight of a vertex set. -/
def weight {n : ℕ} (w : Fin n → ℚ) (I : Finset (Fin n)) : ℚ :=
  ∑ v ∈ I, w v

/-- An independent set that achieves the requested multiplicative guarantee. -/
def IsApproximation {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (ε : ℚ) (I : Finset (Fin n)) : Prop :=
  G.IsIndepSet (I : Set (Fin n)) ∧
    ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) →
      (1 - ε) * weight w J ≤ weight w I

end Lax263307.WeightedIndependentSet
