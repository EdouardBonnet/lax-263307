import Lax263307.LinearRelaxation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
---
title: The components left by deleting a separator
type: definition
---
Deleting a vertex set $S$ partitions the remaining vertices into connected
components. Every undeleted vertex belongs to exactly one part, and every
edge with undeleted endpoints has both endpoints in one part. These are the
properties used to combine the recursive independent sets.

# Formalization notes

`Partition` also permits grouping connected components together. Its parts
are finite sets in the original vertex type. The proof package constructs
the canonical partition into connected components of $G-S$.
-/

namespace Lax263307.SeparatorComponents

/-- A partition of the undeleted vertices, closed under undeleted edges. -/
structure Partition {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (ι : Type) where
  /-- The original vertices in each part. -/
  vertices : ι → Finset (Fin n)
  /-- Parts exclude the deleted vertices. -/
  outside : ∀ i v, v ∈ vertices i → v ∉ S
  /-- Every undeleted vertex belongs to exactly one part. -/
  unique : ∀ v, v ∉ S → ∃! i, v ∈ vertices i
  /-- No undeleted edge leaves a part. -/
  closed : ∀ i u v, u ∈ vertices i → v ∉ S → G.Adj u v → v ∈ vertices i

/-- The recursive answer is the union of the answers on the parts. -/
def combine {n : ℕ} {ι : Type} [Fintype ι] (I : ι → Finset (Fin n)) :
    Finset (Fin n) := Finset.univ.biUnion I

end Lax263307.SeparatorComponents
