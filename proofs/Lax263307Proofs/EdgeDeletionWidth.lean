import Lax263307.EdgeDeletionWidth
import Mathlib.Tactic

namespace Lax263307Proofs.EdgeDeletionWidth

open Lax228581.Treewidth

noncomputable def restoreCoveredEdges {n : ℕ} {G H : SimpleGraph (Fin n)}
    (X : Finset (Fin n))
    (covered : ∀ u v, G.Adj u v → H.Adj u v ∨ u ∈ X ∨ v ∈ X)
    (D : TreeDecomposition H) : TreeDecomposition G := by
  classical
  exact
    { Node := D.Node
      nodeFintype := D.nodeFintype
      tree := D.tree
      isTree := D.isTree
      bag := fun i => X ∪ D.bag i
      vertex_mem_bag := by
        intro v
        obtain ⟨i, hi⟩ := D.vertex_mem_bag v
        exact ⟨i, Finset.mem_union_right X hi⟩
      edge_mem_bag := by
        intro u v huv
        rcases covered u v huv with h | hu | hv
        · obtain ⟨i, hiu, hiv⟩ := D.edge_mem_bag h
          exact ⟨i, Finset.mem_union_right X hiu, Finset.mem_union_right X hiv⟩
        · obtain ⟨i, hi⟩ := D.vertex_mem_bag v
          exact ⟨i, Finset.mem_union_left _ hu, Finset.mem_union_right X hi⟩
        · obtain ⟨i, hi⟩ := D.vertex_mem_bag u
          exact ⟨i, Finset.mem_union_right X hi, Finset.mem_union_left _ hv⟩
      bag_indices_connected := by
        intro v
        by_cases hv : v ∈ X
        · have hset : {i | v ∈ X ∪ D.bag i} = Set.univ := by ext i; simp [hv]
          rw [hset]
          exact (SimpleGraph.induceUnivIso D.tree).connected_iff.mpr D.isTree.connected
        · have hset : {i | v ∈ X ∪ D.bag i} = {i | v ∈ D.bag i} := by ext i; simp [hv]
          rw [hset]
          exact D.bag_indices_connected v }

/--
---
conclusion: Lax263307.EdgeDeletionWidth.restore_edges
---
Choose the first endpoint of each deleted unordered pair. Their image has
cardinality at most the number of deleted edges and meets every deleted edge.
Add this image to every bag, restoring coverage while preserving connected
bag indices. Bound each enlarged bag by the sum of its two constituent sizes.
-/
theorem restore_edges {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n)))
    (w : ℕ) (width : HasTreewidthAtMost (G.deleteEdges (↑F : Set (Sym2 (Fin n)))) w) :
    HasTreewidthAtMost G (w + F.card) := by
  classical
  let H := G.deleteEdges (↑F : Set (Sym2 (Fin n)))
  let X := F.image fun e => e.out.1
  have hcovered : ∀ u v, G.Adj u v → H.Adj u v ∨ u ∈ X ∨ v ∈ X := by
    intro u v huv
    by_cases he : s(u, v) ∈ F
    · have hx : s(u, v).out.1 ∈ X := Finset.mem_image.mpr ⟨s(u, v), he, rfl⟩
      have hmem : s(u, v).out.1 = u ∨ s(u, v).out.1 = v :=
        Sym2.mem_iff.mp (Sym2.out_fst_mem s(u, v))
      rcases hmem with hu | hv
      · exact Or.inr (Or.inl (hu ▸ hx))
      · exact Or.inr (Or.inr (hv ▸ hx))
    · exact Or.inl (by simpa [H, SimpleGraph.deleteEdges_adj] using And.intro huv he)
  obtain ⟨D, hD⟩ := width
  refine ⟨restoreCoveredEdges X hcovered D, ?_⟩
  intro i
  have hX : X.card ≤ F.card := Finset.card_image_le
  change (X ∪ D.bag i).card ≤ w + F.card + 1
  have hbag := Finset.card_union_le X (D.bag i)
  have hi := hD i
  omega

end Lax263307Proofs.EdgeDeletionWidth
