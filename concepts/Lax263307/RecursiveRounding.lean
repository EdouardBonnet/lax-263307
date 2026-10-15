import Lax263307.SeparatorComponents
import Lax263307.ComponentCuts

/-!
---
title: Combining independent sets on separated parts
type: lemma
---
Independent sets contained in distinct parts of a separator partition have
no edges between them. Their union is independent, and its cardinality is
the sum of their cardinalities.

# Attribution

Bonnet–Chang, the union step in the proof of Lemma 14.
-/

namespace Lax263307.RecursiveRounding

open LinearRelaxation SeparatorComponents

/-- Independent answers on different parts combine, and their sizes add. -/
axiom combine_independent {n : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (P : Partition G S ι)
    (I : ι → Finset (Fin n)) (inside : ∀ i, I i ⊆ P.vertices i)
    (independent : ∀ i, G.IsIndepSet (I i : Set (Fin n))) :
    G.IsIndepSet (combine I : Set (Fin n)) ∧ (combine I).card = ∑ i, (I i).card

end Lax263307.RecursiveRounding
