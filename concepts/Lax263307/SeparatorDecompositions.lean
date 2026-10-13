import Lax263307.SeparatorComponents
import Lax263307.EdgeSublinearSeparators
import Lax263307.RecursionDepth
import Lax228581.Treewidth

/-!
---
title: Tree decompositions from recursive balanced separators
type: theorem
---
Attach the decompositions of the parts below a new root bag containing the
separator, and add the separator to every child bag. The resulting bags have
size at most the separator size plus the largest child bag. Recursing on
balanced parts costs at most one separator bound per recursion level.

# Formalization notes

The component trees may have different finite node types. The joining tree
uses a disjoint dependent sum of these types and one additional root. The
recursive bound keeps its logarithmic depth explicit; conversion to an
edge-only sublinear bound is a separate step.
-/

namespace Lax263307.SeparatorDecompositions

open GraphClasses EdgeSublinearSeparators SeparatorComponents Lax228581.Treewidth

/-- Join the component decompositions below a separator root. -/
axiom glue_bound {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    {ι : Type} [Fintype ι] (P : Partition G S ι)
    (D : ∀ i, TreeDecomposition (G.induce (↑(P.vertices i) : Set (Fin n))))
    (B : ℕ) (bound : ∀ i j, ((D i).bag j).card ≤ B) :
    ∃ E : TreeDecomposition G, ∀ j, (E.bag j).card ≤ S.card + B

/-- Balanced recursive separators give a logarithmic depth bag bound. -/
axiom recursive_bag_bound (C : GraphClass) (hereditary : IsHereditary C)
    (B : ℕ → ℕ) (monotone : Monotone B) (positive : ∀ m, 1 ≤ B m)
    (separators : ∀ n (G : SimpleGraph (Fin n)), G ∈ C n →
      ∃ S : Finset (Fin n), IsBalancedSeparator G S ∧ S.card ≤ B G.edgeSet.ncard)
    {n : ℕ} (G : SimpleGraph (Fin n)) (member : G ∈ C n) :
    ∃ D : TreeDecomposition G, ∀ j,
      (D.bag j).card ≤ B G.edgeSet.ncard * (RecursionDepth.depth n + 1)

end Lax263307.SeparatorDecompositions
