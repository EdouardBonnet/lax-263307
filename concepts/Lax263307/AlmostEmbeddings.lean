import Lax263307.ConnectedRepresentations
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
---
title: Treewidth transfer through an almost-embedding
type: lemma
---
An almost-embedding maps each vertex of $H$ into $G$ and assigns to each edge
a connected vertex set joining its mapped endpoints. Sets assigned to
nonincident edges are disjoint. If $H$ has maximum degree at most $d$ and
no isolated vertices, a decomposition of $G$ with bags of size at most $w$
gives a decomposition of $H$ with bags of size at most $2dw$.

# Formalization notes

The connected vertex sets can in particular be the supports of the simple
paths in the paper. This slightly more general definition keeps precisely
the properties needed for tree-decomposition transfer. Mapped vertices need
not be distinct, and singleton routes are allowed. An induced almost-embedding
also forbids edges between routes assigned to nonincident edges.
-/

namespace Lax263307.AlmostEmbeddings

open scoped Classical

open Lax228581.Treewidth

/-- A connected route for every edge, disjoint for nonincident edges. -/
structure AlmostEmbedding {t n : ℕ} (H : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) where
  /-- Vertex images, with no injectivity requirement. -/
  vertexMap : Fin t → Fin n
  /-- Host vertices on each route. -/
  route : H.edgeSet → Finset (Fin n)
  /-- Each route is nonempty and connected. -/
  connected : ∀ e, (G.induce (↑(route e) : Set (Fin n))).Connected
  /-- A route contains the images of its edge's endpoints. -/
  endpoints : ∀ e v, v ∈ e.val → vertexMap v ∈ route e
  /-- Routes of nonincident edges share no host vertex. -/
  disjoint : ∀ e f, Disjoint e.val.toFinset f.val.toFinset → Disjoint (route e) (route f)

/-- In addition, nonincident routes have no edges between them in the host. -/
def IsInduced {t n : ℕ} {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) : Prop :=
  ∀ e f, Disjoint e.val.toFinset f.val.toFinset →
    ∀ a ∈ E.route e, ∀ b ∈ E.route f, ¬G.Adj a b

/-- The union of all routes incident to one represented vertex. -/
noncomputable def vertexCarrier {t n : ℕ} {H : SimpleGraph (Fin t)}
    {G : SimpleGraph (Fin n)} (E : AlmostEmbedding H G) (v : Fin t) : Finset (Fin n) :=
  Finset.univ.biUnion fun e : H.edgeSet => if v ∈ e.val then E.route e else ∅

/-- An almost-embedding transfers decompositions with at most factor `2d` loss. -/
axiom transfer_decomposition {t n : ℕ} (H : SimpleGraph (Fin t))
    [DecidableRel H.Adj] (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G)
    (d w : ℕ) (degree_bound : ∀ v, H.degree v ≤ d)
    (no_isolates : ∀ v, ¬H.IsIsolated v)
    (D : TreeDecomposition G) (bag_bound : ∀ i, (D.bag i).card ≤ w) :
    ∃ D' : TreeDecomposition H, ∀ i, (D'.bag i).card ≤ 2 * d * w

end Lax263307.AlmostEmbeddings
