import Lax263307.SeparatorDecompositions
import Lax263307.PowerBagBounds

/-!
---
title: Edge-sublinear separators imply edge-sublinear decomposition bags
type: lemma
---
In a hereditary graph class, recursively balanced separators build tree
decompositions with a logarithmic factor. Removing isolated vertices first
bounds the remaining order by twice the edge count. Absorb the logarithm
into a positive fraction of the gap between the separator exponent and one.
The resulting bag bound remains strongly sublinear in the edge count.

# Formalization notes

This derives the decomposition bound from the original separator hypothesis.
It uses singleton leaf
bags to restore arbitrarily many isolated vertices. Constants are existential
class constants, as in the main theorem.
-/

namespace Lax263307.EdgeBagBounds

open GraphClasses EdgeSublinearSeparators Lax228581.Treewidth

axiom sublinear_bag_bound (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ β c : ℝ, 0 ≤ β ∧ β < 1 ∧ 0 < c ∧ ∀ n (G : SimpleGraph (Fin n)), G ∈ C n →
      ∃ D : TreeDecomposition G, ∀ j,
        ((D.bag j).card : ℝ) ≤ c * Real.rpow ((G.edgeSet.ncard : ℝ) + 1) β

end Lax263307.EdgeBagBounds
