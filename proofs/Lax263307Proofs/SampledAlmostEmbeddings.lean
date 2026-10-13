import Lax263307.SampledAlmostEmbeddings
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Tactic

namespace Lax263307Proofs.SampledAlmostEmbeddings


open Lax263307.RouteDistributions Lax263307.CoupledRouteSampling Lax263307.CoupledSamplingBounds
open Lax263307.AlmostEmbeddings

theorem route_connected {n : ℕ} (G : SimpleGraph (Fin n)) (Q : List (Fin n))
    (nonempty : Q ≠ []) (chain : Q.IsChain G.Adj) :
    (G.induce (↑Q.toFinset : Set (Fin n))).Connected := by
  let W := SimpleGraph.Walk.ofSupport Q nonempty chain
  have h := W.connected_induce_support
  have hs : W.support = Q := SimpleGraph.Walk.support_ofSupport nonempty chain
  rw [hs] at h
  have hset : (↑Q.toFinset : Set (Fin n)) = {v | v ∈ Q} := by ext v; simp
  rwa [← hset] at h

theorem edge_endpoints_distinct {t : ℕ} (H : SimpleGraph (Fin t)) (e : H.edgeSet) :
    e.val.out.1 ≠ e.val.out.2 := by
  have h : H.Adj e.val.out.1 e.val.out.2 := by
    change s(e.val.out.1, e.val.out.2) ∈ H.edgeSet
    have heq : e.val = s(e.val.out.1, e.val.out.2) := e.val.out_eq.symm
    rw [← heq]
    exact e.property
  exact H.ne_of_adj h

theorem disjoint_endpoints {t : ℕ} (H : SimpleGraph (Fin t)) (e f : H.edgeSet)
    (disjoint : Disjoint e.val.toFinset f.val.toFinset) :
    Function.Injective ![e.val.out.1, e.val.out.2, f.val.out.1, f.val.out.2] := by
  classical
  have hxy := edge_endpoints_distinct H e
  have huv := edge_endpoints_distinct H f
  have he₁ : e.val.out.1 ∈ e.val.toFinset := Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _)
  have he₂ : e.val.out.2 ∈ e.val.toFinset := Sym2.mem_toFinset.mpr (Sym2.out_snd_mem _)
  have hf₁ : f.val.out.1 ∈ f.val.toFinset := Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _)
  have hf₂ : f.val.out.2 ∈ f.val.toFinset := Sym2.mem_toFinset.mpr (Sym2.out_snd_mem _)
  have cross (x y : Fin t) (hx : x ∈ e.val.toFinset) (hy : y ∈ f.val.toFinset) : x ≠ y := by
    intro h
    subst y
    exact Finset.disjoint_left.mp disjoint hx hy
  have h₁ := cross _ _ he₁ hf₁
  have h₂ := cross _ _ he₁ hf₂
  have h₃ := cross _ _ he₂ hf₁
  have h₄ := cross _ _ he₂ hf₂
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> aesop

/--
---
conclusion: Lax263307.SampledAlmostEmbeddings.exists_induced_almost_embedding
---
Enumerate source edges and apply the good-sample theorem to their endpoint
maps. Positive probability fixes shared endpoint images and makes every
route a simple graph walk. Disjoint source edges have four distinct
endpoints, so the good event forbids both route intersection and host
adjacency. Reindex the total route-size sum back to unordered source edges.
-/
theorem exists_induced_almost_embedding {t n q : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Distribution G q) (hn : 0 < n)
    (M : ℝ) (positive : 0 < M)
    (bad_budget : (H.edgeSet.ncard : ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling) ≤ 1 / 4)
    (length_budget : (H.edgeSet.ncard : ℝ) * Lax263307.PathSampling.expectedSize D.toSampling ≤ M) :
    ∃ E : AlmostEmbedding H G, IsInduced E ∧ (∑ e, ((E.route e).card : ℝ)) ≤ 4 * M := by
  classical
  let m := Fintype.card H.edgeSet
  let idx : H.edgeSet ≃ Fin m := Fintype.equivFin H.edgeSet
  let a : Fin m → Fin t := fun i => (idx.symm i).val.out.1
  let b : Fin m → Fin t := fun i => (idx.symm i).val.out.2
  have hedgecard : m = H.edgeSet.ncard := Set.fintypeCard_eq_ncard H.edgeSet
  have nonloop (i : Fin m) : a i ≠ b i := edge_endpoints_distinct H (idx.symm i)
  have hbad : (m : ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling) ≤ 1 / 4 := by simpa [hedgecard] using bad_budget
  have hlen : (m : ℝ) * Lax263307.PathSampling.expectedSize D.toSampling ≤ M := by simpa [hedgecard] using length_budget
  obtain ⟨φ, ψ, hp, hgood, hcost⟩ := good_route_sample G D hn a b nonloop M positive hbad hlen
  have hvalid := joint_valid D hn a b φ ψ hp
  let E : AlmostEmbedding H G := {
    vertexMap := φ
    route := fun e => (D.route (ψ (idx e))).toFinset
    connected := by
      intro e
      have h := hvalid (idx e)
      have hne : D.route (ψ (idx e)) ≠ [] := by intro hn; simp [hn] at h
      exact route_connected G _ hne h.2.2.2
    endpoints := by
      intro e v hv
      have hev : v = e.val.out.1 ∨ v = e.val.out.2 := by
        rw [← e.val.out_eq] at hv
        exact Sym2.mem_iff.mp hv
      have h := hvalid (idx e)
      rcases hev with rfl | rfl
      · apply List.mem_toFinset.mpr
        have hs : (D.route (ψ (idx e))).head? = some (φ e.val.out.1) := by simpa [a] using h.1
        exact List.mem_of_head? hs
      · apply List.mem_toFinset.mpr
        have hs : (D.route (ψ (idx e))).getLast? = some (φ e.val.out.2) := by simpa [b] using h.2.1
        exact List.mem_of_getLast? hs
    disjoint := by
      intro e f hef
      have hi : Function.Injective ![a (idx e), b (idx e), a (idx f), b (idx f)] := by
        simpa [a, b] using disjoint_endpoints H e f hef
      exact not_not.mp ((not_or.mp (hgood (idx e) (idx f) hi)).1) }
  refine ⟨E, ?_, ?_⟩
  · intro e f hef u hu v hv huv
    have hi : Function.Injective ![a (idx e), b (idx e), a (idx f), b (idx f)] := by
      simpa [a, b] using disjoint_endpoints H e f hef
    exact (not_or.mp (hgood (idx e) (idx f) hi)).2 ⟨u, hu, v, hv, huv⟩
  · have hsum : (∑ e : H.edgeSet, ((E.route e).card : ℝ)) =
        ∑ i : Fin m, ((D.route (ψ i)).toFinset.card : ℝ) := by
      exact Fintype.sum_equiv idx _ _ (fun e => rfl)
    rw [hsum]
    exact hcost


end Lax263307Proofs.SampledAlmostEmbeddings
