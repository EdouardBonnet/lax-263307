import Lax263307.InducedEmbeddingWidth
import Mathlib.Tactic

namespace Lax263307Proofs.InducedEmbeddingWidth

open Lax263307.AlmostEmbeddings Lax263307.InducedRouteEdges Lax228581.Treewidth
open Lax263307.GraphClasses Lax263307.InducedEmbeddingWidth

/--
---
conclusion: Lax263307.InducedEmbeddingWidth.transfer_class_bound
---
Restrict the host to the route union, which belongs to the class by
heredity. Bound its induced edge count, apply the monotone class bag bound,
and transfer back to the source with singleton bags for isolated vertices.
An empty route union makes the source edgeless and gives bag size one.
-/
theorem transfer_class_bound {t n : ℕ} (C : GraphClass) (hereditary : IsHereditary C)
    (W : ℕ → ℕ) (monotone : Monotone W) (class_bound : HasBagBound C W)
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (G : SimpleGraph (Fin n))
    (member : G ∈ C n) (E : AlmostEmbedding H G) (induced : IsInduced E) (d L : ℕ)
    (degree_bound : ∀ v, H.degree v ≤ d) (length_bound : ∀ e, (E.route e).card ≤ L) :
    ∃ D : TreeDecomposition H, ∀ i, (D.bag i).card ≤
      max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) := by
  classical
  by_cases hu : (routeUnion E).Nonempty
  · obtain ⟨r, K, f, E', hE', hcards, hcount⟩ :=
      Lax263307.HostRestriction.restrict_to_route_union H G E induced hu
    have hK : K ∈ C r := hereditary r n K G member ⟨f⟩
    have hsmall : K.edgeSet.ncard ≤ d * H.edgeSet.ncard * L ^ 2 := by
      rw [hcount]
      exact Lax263307.InducedRouteEdges.edge_bound H G E d L induced degree_bound length_bound
    obtain ⟨DK, hDK⟩ := class_bound r K hK
    have hbags : ∀ i, (DK.bag i).card ≤ W (d * H.edgeSet.ncard * L ^ 2) :=
      fun i => (hDK i).trans (monotone hsmall)
    exact Lax263307.IsolatedEmbeddingTransfer.transfer_decomposition H K E' d _ degree_bound DK hbags
  · have he : routeUnion E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu
    have isolated (v : Fin t) : H.IsIsolated v := by
      intro u huv
      let e : H.edgeSet := ⟨s(v, u), huv⟩
      have hr : E.vertexMap v ∈ routeUnion E := Finset.mem_biUnion.mpr
        ⟨e, Finset.mem_univ _, E.endpoints e v (Sym2.mem_mk_left _ _)⟩
      simp [he] at hr
    have zero_degree (v : Fin t) : H.degree v ≤ 0 := by
      rw [(H.degree_eq_zero v).mpr (isolated v)]
    obtain ⟨DG, hDG⟩ := class_bound n G member
    obtain ⟨DH, hDH⟩ := Lax263307.IsolatedEmbeddingTransfer.transfer_decomposition H G E 0 _ zero_degree DG hDG
    refine ⟨DH, ?_⟩
    intro i
    have hb : (DH.bag i).card ≤ 1 := by simpa using hDH i
    exact hb.trans (le_max_left _ _)

theorem transfer_after_pruning {t n : ℕ} (C : GraphClass) (hereditary : IsHereditary C)
    (W : ℕ → ℕ) (monotone : Monotone W) (class_bound : HasBagBound C W)
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (G : SimpleGraph (Fin n))
    (member : G ∈ C n) (E : AlmostEmbedding H G) (induced : IsInduced E) (d L : ℕ)
    (degree_bound : ∀ v, H.degree v ≤ d) :
    ∃ D : TreeDecomposition H, ∀ i, (D.bag i).card ≤
      max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + (Lax263307.RoutePruning.longEdges E L).card := by
  classical
  let F := Lax263307.RoutePruning.longEdges E L
  let K := H.deleteEdges (↑F : Set (Sym2 (Fin t)))
  obtain ⟨E', hinduced, hshort⟩ := Lax263307.RoutePruning.prune_routes H G E induced L
  have degK (v : Fin t) : K.degree v ≤ d :=
    (K.degree_le_of_le (H.deleteEdges_le _)).trans (degree_bound v)
  obtain ⟨DK, hDK⟩ := Lax263307.InducedEmbeddingWidth.transfer_class_bound C hereditary W monotone class_bound K G member E' hinduced d L degK hshort
  have hcount : K.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_mono (SimpleGraph.edgeSet_mono (H.deleteEdges_le _))
  let B := max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2))
  have hB : 1 ≤ B := le_max_left _ _
  have hbags (i : DK.Node) : (DK.bag i).card ≤ B := by
    apply (hDK i).trans
    apply max_le_max (le_refl 1)
    apply Nat.mul_le_mul_left
    apply monotone
    exact Nat.mul_le_mul_right (L ^ 2) (Nat.mul_le_mul_left d hcount)
  have hwidth : HasTreewidthAtMost K (B - 1) := by
    refine ⟨DK, ?_⟩
    intro i
    simpa only [Nat.sub_add_cancel hB] using hbags i
  obtain ⟨DH, hDH⟩ := Lax263307.EdgeDeletionWidth.restore_edges H F (B - 1) hwidth
  refine ⟨DH, ?_⟩
  intro i
  have h := hDH i
  change (DH.bag i).card ≤ B + F.card
  omega

/--
---
conclusion: Lax263307.InducedEmbeddingWidth.treewidth_after_pruning
---
Discard long routes and transfer the class width bound to the remaining
source graph. Its degrees and edge count cannot increase. Restore deleted
edges with the proved edge-deletion bound, then use the definition of
treewidth as the minimum admitted decomposition width.
-/
theorem treewidth_after_pruning {t n : ℕ} (C : GraphClass) (hereditary : IsHereditary C)
    (W : ℕ → ℕ) (monotone : Monotone W) (class_bound : HasBagBound C W)
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (G : SimpleGraph (Fin n))
    (member : G ∈ C n) (E : AlmostEmbedding H G) (induced : IsInduced E) (d L : ℕ)
    (degree_bound : ∀ v, H.degree v ≤ d) :
    treewidth H + 1 ≤ max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) +
      (Lax263307.RoutePruning.longEdges E L).card := by
  classical
  let B := max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + (Lax263307.RoutePruning.longEdges E L).card
  have hB : 1 ≤ B := by dsimp [B]; omega
  obtain ⟨D, hD⟩ := transfer_after_pruning C hereditary W monotone class_bound H G member E induced d L degree_bound
  have hwidth : HasTreewidthAtMost H (B - 1) := by
    refine ⟨D, ?_⟩
    intro i
    simpa only [Nat.sub_add_cancel hB] using hD i
  have hw : treewidth H ≤ B - 1 := Nat.sInf_le hwidth
  change treewidth H + 1 ≤ B
  omega

/--
---
conclusion: Lax263307.InducedEmbeddingWidth.sampled_width_bound
---
Choose the proved induced almost-embedding with total route size at most
4M. The long-route count bounds L times the number of removed edges,
and the pruning width bound gives the quantitative obstruction.
-/
theorem sampled_width_bound {t n q : ℕ} (C : GraphClass) (hereditary : IsHereditary C)
    (W : ℕ → ℕ) (monotone : Monotone W) (class_bound : HasBagBound C W)
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (member : G ∈ C n) (D : Lax263307.RouteDistributions.Distribution G q) (hn : 0 < n)
    (d L : ℕ) (degree_bound : ∀ v, H.degree v ≤ d) (M : ℝ) (positive : 0 < M)
    (bad_budget : (H.edgeSet.ncard : ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling) ≤ 1 / 4)
    (length_budget : (H.edgeSet.ncard : ℝ) * Lax263307.PathSampling.expectedSize D.toSampling ≤ M) :
    ∃ removed : ℕ, (L : ℝ) * removed ≤ 4 * M ∧
      treewidth H + 1 ≤ max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + removed := by
  classical
  obtain ⟨E, hinduced, hcost⟩ := Lax263307.SampledAlmostEmbeddings.exists_induced_almost_embedding H G D hn M positive bad_budget length_budget
  let removed := (Lax263307.RoutePruning.longEdges E L).card
  refine ⟨removed, ?_, Lax263307.InducedEmbeddingWidth.treewidth_after_pruning C hereditary W monotone class_bound H G member E hinduced d L degree_bound⟩
  have hcount : (L : ℝ) * removed ≤ ∑ e, ((E.route e).card : ℝ) := by
    exact_mod_cast Lax263307.RoutePruning.long_edge_count H G E L
  exact hcount.trans hcost


end Lax263307Proofs.InducedEmbeddingWidth
