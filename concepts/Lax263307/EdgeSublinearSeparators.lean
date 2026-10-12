import Lax263307.GraphClasses
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
---
title: Strongly edge-sublinear separators
type: definition
---
A balanced separator of an $n$-vertex graph $G$ is a vertex set $S$ such
that every connected component of $G-S$ has at most $2n/3$ vertices.
A graph class has strongly edge-sublinear separators if there are constants
$c>0$ and $0\le b<1$ such that each of its $m$-edge graphs has a balanced
separator of size at most $c(m+1)^b$.

# Formalization notes

The $+1$ makes the paper's asymptotic bound $O(m^b)$ meaningful at $m=0$:
a singleton graph needs a separator of size one under the stated balance
condition. For $m\ge1$ this normalization is equivalent to $O(m^b)$;
edgeless graphs of order at least two have an empty balanced separator.
Edges are counted as unordered pairs, using mathlib's edge set.
The balance inequality uses integers, $3|K|\le2n$, without rounding.
Heredity is a separate hypothesis in the main theorem.
-/

namespace Lax263307.EdgeSublinearSeparators

open GraphClasses

/-- Each component after deleting `S` contains at most two thirds of the vertices. -/
def IsBalancedSeparator {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : Prop :=
  ∀ K : (G.induce (↑S : Set (Fin n))ᶜ).ConnectedComponent,
    3 * K.supp.ncard ≤ 2 * n

/-- A uniform separator bound sublinear in the number of edges. -/
def HasStronglyEdgeSublinearSeparators (C : GraphClass) : Prop :=
  ∃ (b c : ℝ), 0 ≤ b ∧ b < 1 ∧ 0 < c ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ C n →
      ∃ S : Finset (Fin n), IsBalancedSeparator G S ∧
        (S.card : ℝ) ≤ c * Real.rpow ((G.edgeSet.ncard : ℝ) + 1) b

end Lax263307.EdgeSublinearSeparators
