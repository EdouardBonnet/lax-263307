import Lax263307.IsolatedEmbeddingTransfer
import Lax263307Proofs.TreeExtensions
import Mathlib.Tactic

namespace Lax263307Proofs.IsolatedEmbeddingTransfer

open Lax263307.AlmostEmbeddings Lax228581.Treewidth
open Lax263307Proofs.TreeExtensions

noncomputable def restrictSource {r t n : ℕ} {K : SimpleGraph (Fin r)}
    {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)} (f : K ↪g H)
    (E : AlmostEmbedding H G) : AlmostEmbedding K G where
  vertexMap := fun v => E.vertexMap (f v)
  route := fun e => E.route (f.toHom.mapEdgeSet e)
  connected := fun e => E.connected _
  endpoints := by
    intro e v hv
    apply E.endpoints
    exact Sym2.mem_map.mpr ⟨v, hv, rfl⟩
  disjoint := by
    intro e h hd
    apply E.disjoint
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨u, hu, huz⟩ := Sym2.mem_map.mp (Sym2.mem_toFinset.mp hz)
    obtain ⟨v, hv, hvz⟩ := Sym2.mem_map.mp (Sym2.mem_toFinset.mp hz')
    have huv : u = v := f.injective (huz.trans hvz.symm)
    subst v
    exact Finset.disjoint_left.mp hd (Sym2.mem_toFinset.mpr hu) (Sym2.mem_toFinset.mpr hv)

theorem embedding_degree {r t : ℕ} (K : SimpleGraph (Fin r)) [DecidableRel K.Adj]
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (f : K ↪g H) (v : Fin r) :
    K.degree v ≤ H.degree (f v) := by
  classical
  rw [← K.card_neighborSet_eq_degree v, ← H.card_neighborSet_eq_degree (f v)]
  apply Fintype.card_le_of_injective (f.toHom.mapNeighborSet v)
  intro a b h
  apply Subtype.ext
  exact f.injective (congrArg Subtype.val h)

/--
---
conclusion: Lax263307.IsolatedEmbeddingTransfer.transfer_decomposition
---
Relabel the nonisolated induced subgraph by Fin and restrict the source
almost-embedding along its induced embedding. Degrees cannot increase and
this subgraph has no isolated vertices. Apply the proved transfer, pull the
decomposition back to the induced graph, and attach singleton bags for the
omitted isolated vertices using the proved tree-extension construction.
-/
theorem transfer_decomposition {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (d w : ℕ)
    (degree_bound : ∀ v, H.degree v ≤ d)
    (D : TreeDecomposition G) (bag_bound : ∀ i, (D.bag i).card ≤ w) :
    ∃ D' : TreeDecomposition H, ∀ i, (D'.bag i).card ≤ max 1 (2 * d * w) := by
  classical
  let S : Set (Fin t) := {v | ¬H.IsIsolated v}
  let r := Fintype.card S
  let e : S ≃ Fin r := Fintype.equivFin S
  let f : Fin r → Fin t := fun v => (e.symm v).val
  let K := H.comap f
  let emb : K ↪g H := {
    toFun := f
    inj' := by intro u v h; exact e.symm.injective (Subtype.ext h)
    map_rel_iff' := by intro u v; rfl }
  have no_isolates (v : Fin r) : ¬K.IsIsolated v := by
    have hv : ¬H.IsIsolated (f v) := (e.symm v).property
    obtain ⟨u, hu⟩ : ∃ u, H.Adj (f v) u := by simpa [SimpleGraph.IsIsolated] using hv
    have hau : u ∈ S := by
      intro h
      exact h (f v) hu.symm
    let z := e ⟨u, hau⟩
    have hz : f z = u := by simp [f, z]
    intro h
    apply h z
    change H.Adj (f v) (f z)
    rwa [hz]
  have degree_K (v : Fin r) : K.degree v ≤ d :=
    (embedding_degree K H emb v).trans (degree_bound _)
  obtain ⟨DK, hDK⟩ := Lax263307.AlmostEmbeddings.transfer_decomposition K G
    (restrictSource emb E) d w degree_K no_isolates D bag_bound
  let inv : H.induce S ↪g K := {
    toFun := e
    inj' := e.injective
    map_rel_iff' := by
      intro u v
      change H.Adj (f (e u)) (f (e v)) ↔ H.Adj u.val v.val
      simp [f] }
  let DS := pullback inv DK
  have isolated (v : Fin t) (hv : v ∉ S) : H.IsIsolated v := by simpa [S] using hv
  refine ⟨extendIsolated S isolated DS, ?_⟩
  apply extendIsolated_card S isolated DS _ (le_max_left _ _)
  intro i
  exact (pullback_card inv DK i).trans ((hDK i).trans (le_max_right _ _))


end Lax263307Proofs.IsolatedEmbeddingTransfer
