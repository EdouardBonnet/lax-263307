import Lax228581.Treewidth
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.Fin

/-!
---
title: Treewidth loss under edge deletion
type: lemma
---
Deleting $q$ edges reduces treewidth by at most $q$. Choose one endpoint of
each deleted edge and add all chosen vertices to every bag of a decomposition
of the remaining graph. This restores edge coverage and increases bag sizes
by at most $q$.

# Attribution

The edge-deletion estimate used to retain linear treewidth after discarding
long sampled paths in Bonnet–Chang, Lemma 11.
-/

namespace Lax263307.EdgeDeletionWidth

open Lax228581.Treewidth

/-- A width bound after edge deletion gives this bound for the original graph. -/
axiom restore_edges {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n)))
    (w : ℕ) (width : HasTreewidthAtMost (G.deleteEdges (↑F : Set (Sym2 (Fin n)))) w) :
    HasTreewidthAtMost G (w + F.card)

end Lax263307.EdgeDeletionWidth
