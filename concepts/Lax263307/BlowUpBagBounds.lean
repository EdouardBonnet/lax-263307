import Lax263307.EdgeBagBounds
import Lax263307.BlowUpClasses
import Lax263307.BlowUpDeletion

/-!
---
title: Sublinear bag bounds survive independent blow-ups
type: lemma
---
The independent blow-up closure of a hereditary class with strongly
edge-sublinear separators also has edge-sublinear decomposition bags.
Restrict the original host to vertices used by the projection. Choosing
one representative in each fibre embeds this host into the blow-up, so
its edge count cannot exceed that of the blow-up. Optimize degree deletion
and bounded-fibre lifting, then convert the resulting real exponent to
an integer power bound.

# Formalization notes

Arbitrary projection fibres, including empty fibres, are allowed. Relabel
used host vertices and enumerate each fibre to identify the graph with an
explicit copy graph. The original host need not have at most as many edges
until its unused vertices are removed. These existential constructions
are structural analysis; the algorithm does not build decomposition bags.
-/

namespace Lax263307.BlowUpBagBounds

open PowerBagBounds (HasPowerBagBound)
open GraphClasses EdgeSublinearSeparators BlowUpClasses Lax228581.Treewidth

axiom blowup_sublinear_bag_bound (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ β c : ℝ, 0 ≤ β ∧ β < 1 ∧ 0 < c ∧ ∀ m (H : SimpleGraph (Fin m)), H ∈ blowUpClass C m →
      ∃ D : TreeDecomposition H, ∀ j,
        ((D.bag j).card : ℝ) ≤ c * Real.rpow ((H.edgeSet.ncard : ℝ) + 1) β

axiom blowup_power_bag_bound (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ a A : ℕ, 0 < a ∧ 0 < A ∧ HasPowerBagBound (blowUpClass C) a A

end Lax263307.BlowUpBagBounds
