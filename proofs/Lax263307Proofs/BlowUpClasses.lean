import Lax263307.BlowUpClasses

namespace Lax263307Proofs.BlowUpClasses

open Lax263307.GraphClasses Lax263307.IndependentBlowUp Lax263307.BlowUpClasses

/--
---
conclusion: Lax263307.BlowUpClasses.hereditary_closure
---
The independent blow-up closure is closed under induced embeddings.

# Proof strategy

Compose the induced embedding with the existing projection to the host graph.
The embedding and projection both preserve and reflect adjacency.
-/
theorem hereditary_closure (C : GraphClass) : IsHereditary (blowUpClass C) := by
  intro m n H K hK hembedding
  obtain ⟨embedding⟩ := hembedding
  obtain ⟨l, G, hG, projection, hAdj⟩ := hK
  refine ⟨l, G, hG, fun v => projection (embedding v), ?_⟩
  intro u v
  exact embedding.map_adj_iff.symm.trans (hAdj (embedding u) (embedding v))

/--
---
conclusion: Lax263307.BlowUpClasses.copy_graph_mem
---
Every explicitly constructed copy graph, relabeled to a numbered vertex
set, belongs to the independent blow-up closure.

# Proof strategy

Project each labeled copy to its original vertex. By definition of the
comap graph, adjacency is exactly adjacency of these original vertices.
-/
theorem copy_graph_mem (C : GraphClass) {n : ℕ} (G : SimpleGraph (Fin n))
    (member : G ∈ C n) (copies : Fin n → ℕ) (m : ℕ) (labeling : Fin m ≃ Vertex copies) :
    (graph G copies).comap labeling ∈ blowUpClass C m := by
  refine ⟨n, G, member, fun v => (labeling v).1, ?_⟩
  intro u v
  rfl

end Lax263307Proofs.BlowUpClasses
