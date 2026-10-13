import Lax263307.RoutePruning
import Mathlib.Tactic

namespace Lax263307Proofs.RoutePruning

open Lax263307.AlmostEmbeddings Lax263307.RoutePruning

theorem longEdges_mem {t n : ℕ} {H : SimpleGraph (Fin t)} [DecidableRel H.Adj]
    {G : SimpleGraph (Fin n)} (E : AlmostEmbedding H G) (L : ℕ) (e : H.edgeSet) :
    e.val ∈ longEdges E L ↔ L < (E.route e).card := by
  classical
  simp only [longEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, hf, he⟩
    have hfe : f = e := Subtype.ext he
    simpa [hfe] using hf
  · intro h
    exact ⟨e, h, rfl⟩

/--
---
conclusion: Lax263307.RoutePruning.long_edge_count
---
The discarded source edges are a filtered subset of the unordered
edge set. Each has route size at least L. Sum this bound over the
filtered subset and compare with the full nonnegative sum.
-/
theorem long_edge_count {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (L : ℕ) :
    L * (longEdges E L).card ≤ ∑ e : H.edgeSet, (E.route e).card := by
  classical
  let S := Finset.univ.filter fun e : H.edgeSet => L < (E.route e).card
  have hc : (longEdges E L).card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
  rw [hc]
  calc
    L * S.card = ∑ _e ∈ S, L := by simp [Nat.mul_comm]
    _ ≤ ∑ e ∈ S, (E.route e).card := Finset.sum_le_sum fun e he =>
      (Finset.mem_filter.mp he).2.le
    _ ≤ ∑ e : H.edgeSet, (E.route e).card := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S) (fun _ _ _ => Nat.zero_le _)

noncomputable def restrictEdges {t n : ℕ} {K H : SimpleGraph (Fin t)}
    {G : SimpleGraph (Fin n)} (subgraph : K ≤ H) (E : AlmostEmbedding H G) : AlmostEmbedding K G where
  vertexMap := E.vertexMap
  route e := E.route ⟨e.val, SimpleGraph.edgeSet_mono subgraph e.property⟩
  connected _e := E.connected _
  endpoints _e v hv := E.endpoints _ v hv
  disjoint _e _f h := E.disjoint _ _ h

/--
---
conclusion: Lax263307.RoutePruning.prune_routes
---
Restrict the edge routes to the graph obtained by deleting long source
edges. Their connectivity, endpoints, and induced noninteraction remain
valid. A remaining edge cannot have a long route by its deletion predicate.
-/
theorem prune_routes {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (induced : IsInduced E) (L : ℕ) :
    ∃ E' : AlmostEmbedding (H.deleteEdges (↑(longEdges E L) : Set (Sym2 (Fin t)))) G,
      IsInduced E' ∧ (∀ e, (E'.route e).card ≤ L) := by
  classical
  let F := longEdges E L
  let K := H.deleteEdges (↑F : Set (Sym2 (Fin t)))
  let E' := restrictEdges (H.deleteEdges_le (↑F : Set (Sym2 (Fin t)))) E
  refine ⟨E', ?_, ?_⟩
  · intro e f h
    exact induced _ _ h
  · intro e
    let old : H.edgeSet := ⟨e.val, SimpleGraph.edgeSet_mono (H.deleteEdges_le _) e.property⟩
    have he : e.val ∉ F := by
      have h : e.val ∈ H.edgeSet \ (↑F : Set (Sym2 (Fin t))) := by
        simpa only [SimpleGraph.edgeSet_deleteEdges] using e.property
      exact h.2
    have hshort : (E.route old).card ≤ L := by
      by_contra h
      have hlong : L < (E.route old).card := by omega
      exact he ((longEdges_mem E L old).mpr hlong)
    exact hshort


end Lax263307Proofs.RoutePruning
