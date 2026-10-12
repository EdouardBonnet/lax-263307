import Lax263307.BlowUpIndependentSets
import Lax228581.Treewidth

/-!
---
title: Lifting a tree decomposition through a bounded blow-up
type: theorem
---
Suppose $G$ has treewidth at most $w$, and every vertex is replaced by at
most $s$ independent copies. The blow-up has a tree decomposition whose
bags have size at most $s(w+1)$.

# Formalization notes

The original decomposition tree is retained, and each vertex in a bag is
replaced by all its copies. An empty fibre contributes no vertices.
The conclusion is expressed directly as a bag-size bound using the
registered `Lax228581.Treewidth.TreeDecomposition` definition.

# Attribution

Bonnet–Chang, the tree-decomposition construction in the proof of Lemma 16.
-/

namespace Lax263307.BlowUpDecompositions

open IndependentBlowUp Lax228581.Treewidth

/-- Replacing every bag vertex by its copies multiplies bag sizes by at most `s`. -/
axiom bounded_blowup_decomposition {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s w : ℕ) (bounded : ∀ v, copies v ≤ s)
    (width : HasTreewidthAtMost G w) :
    ∃ D : TreeDecomposition (graph G copies), ∀ i, (D.bag i).card ≤ s * (w + 1)

end Lax263307.BlowUpDecompositions
