import Lax228581.Treewidth
import Mathlib.Data.Fintype.Fin

/-!
---
title: Bags meeting a connected vertex set
type: theorem
---
In a tree decomposition, the nodes whose bags meet a nonempty connected
vertex set induce a connected subtree. The bag subtrees of adjacent vertices
intersect in a bag covering their edge, so connected vertex sets give
connected unions of bag subtrees.

# Attribution

The connected-bag observation used in Bonnet–Chang, proof of Lemma 9.
-/

namespace Lax263307.ConnectedBags

open Lax228581.Treewidth

/-- The decomposition nodes whose bags meet `U`. -/
def meetingNodes {n : ℕ} {G : SimpleGraph (Fin n)}
    (D : TreeDecomposition G) (U : Finset (Fin n)) : Set D.Node :=
  {i | ∃ v ∈ U, v ∈ D.bag i}

/-- Connected vertex sets meet a connected collection of decomposition bags. -/
axiom meeting_connected {n : ℕ} (G : SimpleGraph (Fin n))
    (D : TreeDecomposition G) (U : Finset (Fin n))
    (connected : (G.induce (↑U : Set (Fin n))).Connected) :
    (D.tree.induce (meetingNodes D U)).Connected

end Lax263307.ConnectedBags
