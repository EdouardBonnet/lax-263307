import Lax263307.GraphClasses
import Lax263307.IndependentBlowUp

/-!
---
title: Independent blow-up classes are hereditary
type: lemma
---
The independent blow-up closure of a graph class consists of finite graphs
whose vertices project to a member of that class, with adjacency exactly
determined by adjacency of the projected vertices. This closure is hereditary.
The explicitly constructed copy graphs belong to it after relabeling.

# Formalization notes

Projection fibres are independent, and between two fibres all edges or no
edges are present. Empty fibres are allowed, matching the zero multiplicities
in the weighted reduction. With this convention the closure is hereditary
for every original class. For a hereditary original class it agrees with
the paper's convention of nonempty fibres: delete the unused host vertices
before constructing the blow-up.
-/

namespace Lax263307.BlowUpClasses

open GraphClasses IndependentBlowUp

/-- Graphs obtained by independent blow-ups of members, allowing empty fibres. -/
def blowUpClass (C : GraphClass) : GraphClass :=
  fun m => {H | ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ C n ∧
    ∃ projection : Fin m → Fin n,
      ∀ u v, H.Adj u v ↔ G.Adj (projection u) (projection v)}

/-- Restricting an independent blow-up to any induced subgraph remains a blow-up. -/
axiom hereditary_closure (C : GraphClass) : IsHereditary (blowUpClass C)

/-- Relabeling the explicit copy graph places it in the blow-up closure. -/
axiom copy_graph_mem (C : GraphClass) {n : ℕ} (G : SimpleGraph (Fin n))
    (member : G ∈ C n) (copies : Fin n → ℕ) (m : ℕ) (labeling : Fin m ≃ Vertex copies) :
    (graph G copies).comap labeling ∈ blowUpClass C m

end Lax263307.BlowUpClasses
