import Lax263307.WeightedIndependentSet
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators

/-!
---
title: Independent blow-ups and projection
type: definition
---
For a graph $G$ and nonnegative integer multiplicities $t_v$, replace vertex
$v$ by an independent set of $t_v$ copies. Copies of distinct vertices are
adjacent exactly when their original vertices are adjacent. Zero multiplicities
omit vertices. Lift a vertex set by taking all of its copies; project a set
of copies by taking the vertices represented by at least one selected copy.

# Formalization notes

A copy is a pair $(v,i)$ with $0\le i<t_v$. This dependent pair type has
exactly $\sum_v t_v$ elements and admits the usual finite-type instances.
The blow-up graph is the comap of $G$ along the projection to $v$.
The cardinality approximation predicate compares the returned independent
set with every independent set in this finite graph.
-/

namespace Lax263307.IndependentBlowUp

/-- The vertices of an independent blow-up, including possibly empty fibres. -/
abbrev Vertex {n : ℕ} (copies : Fin n → ℕ) := (v : Fin n) × Fin (copies v)

/-- Copies are adjacent precisely when their original vertices are adjacent. -/
def graph {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ) :
    SimpleGraph (Vertex copies) := G.comap fun v => v.1

/-- All copies of a given original vertex set. -/
def lift {n : ℕ} (copies : Fin n → ℕ) (I : Finset (Fin n)) : Finset (Vertex copies) :=
  I.sigma fun _ => Finset.univ

/-- Vertices represented by at least one selected copy. -/
def project {n : ℕ} {copies : Fin n → ℕ} (K : Finset (Vertex copies)) : Finset (Fin n) :=
  K.image fun v => v.1

/-- The usual multiplicative cardinality guarantee on the blow-up graph. -/
def IsCardinalityApproximation {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (δ : ℚ) (K : Finset (Vertex copies)) : Prop :=
  (graph G copies).IsIndepSet (K : Set (Vertex copies)) ∧
    ∀ J : Finset (Vertex copies), (graph G copies).IsIndepSet (J : Set (Vertex copies)) →
      (1 - δ) * (J.card : ℚ) ≤ K.card

end Lax263307.IndependentBlowUp
