import Lax263307.AlmostEmbeddings
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
---
title: Few edges in the graph induced by short routes
type: lemma
---
Suppose an induced almost-embedding of a graph $H$ of maximum degree at most
$d$ uses at most $L$ host vertices per route. The union of its routes has
at most $|E(H)|L$ vertices. Its induced graph has maximum degree at most
$2dL$, and therefore at most $d|E(H)|L^2$ edges.
-/

namespace Lax263307.InducedRouteEdges

open scoped Classical

open AlmostEmbeddings

/-- All host vertices used by some edge route. -/
noncomputable def routeUnion {t n : ℕ} {H : SimpleGraph (Fin t)}
    [DecidableRel H.Adj] {G : SimpleGraph (Fin n)} (E : AlmostEmbedding H G) : Finset (Fin n) :=
  Finset.univ.biUnion E.route

/-- Bounded-length induced routes induce few host edges. -/
axiom edge_bound {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (d L : ℕ)
    (induced : IsInduced E) (degree_bound : ∀ v, H.degree v ≤ d)
    (length_bound : ∀ e, (E.route e).card ≤ L) :
    (G.induce (↑(routeUnion E) : Set (Fin n))).edgeSet.ncard ≤
      d * H.edgeSet.ncard * L ^ 2

end Lax263307.InducedRouteEdges
