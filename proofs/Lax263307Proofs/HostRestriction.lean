import Lax263307.HostRestriction
import Mathlib.Tactic

namespace Lax263307Proofs.HostRestriction

open Lax263307.AlmostEmbeddings Lax263307.InducedRouteEdges

/--
---
conclusion: Lax263307.HostRestriction.restrict_to_route_union
---
Choose a Fin labeling of the route union. Map vertices inside it to their
labels and all other vertices to a fixed label. Every route lies inside
the union, so this map preserves its cardinality, connectivity, endpoints,
and induced noninteraction. The labeling is a graph isomorphism onto the
induced host and therefore preserves the unordered edge count.
-/
theorem restrict_to_route_union {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (induced : IsInduced E)
    (nonempty : (routeUnion E).Nonempty) :
    ∃ r, ∃ K : SimpleGraph (Fin r), ∃ _f : K ↪g G, ∃ E' : AlmostEmbedding H K,
      IsInduced E' ∧ (∀ e, (E'.route e).card = (E.route e).card) ∧
      K.edgeSet.ncard = (G.induce (↑(routeUnion E) : Set (Fin n))).edgeSet.ncard := by
  classical
  let U := routeUnion E
  let S : Set (Fin n) := ↑U
  let r := Fintype.card S
  let idx : S ≃ Fin r := Fintype.equivFin S
  obtain ⟨root, hroot⟩ := nonempty
  let forward : Fin r → Fin n := fun i => (idx.symm i).val
  let backward : Fin n → Fin r := fun v =>
    if hv : v ∈ U then idx ⟨v, hv⟩ else idx ⟨root, hroot⟩
  let K := G.comap forward
  let f : K ↪g G := {
    toFun := forward
    inj' := by intro i j h; exact idx.symm.injective (Subtype.ext h)
    map_rel_iff' := by intro i j; rfl }
  have route_subset (e : H.edgeSet) : E.route e ⊆ U := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hv⟩
  have hf (v : Fin n) (hv : v ∈ U) : forward (backward v) = v := by
    simp [backward, hv, forward]
  have hb_inj (u v : Fin n) (hu : u ∈ U) (hv : v ∈ U) (h : backward u = backward v) : u = v := by
    have hh := congrArg forward h
    rwa [hf u hu, hf v hv] at hh
  let E' : AlmostEmbedding H K := {
    vertexMap := fun v => backward (E.vertexMap v)
    route := fun e => (E.route e).image backward
    connected := by
      intro e
      let map : G.induce (↑(E.route e) : Set (Fin n)) →g
          K.induce (↑((E.route e).image backward) : Set (Fin r)) := {
        toFun := fun v => ⟨backward v.val, Finset.mem_image.mpr ⟨v.val, v.property, rfl⟩⟩
        map_rel' := by
          intro u v huv
          change G.Adj (forward (backward u.val)) (forward (backward v.val))
          rwa [hf u.val (route_subset e u.property), hf v.val (route_subset e v.property)] }
      apply (E.connected e).map map
      rintro ⟨z, hz⟩
      obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz
      exact ⟨⟨v, hv⟩, Subtype.ext hvz⟩
    endpoints := by
      intro e v hv
      exact Finset.mem_image.mpr ⟨E.vertexMap v, E.endpoints e v hv, rfl⟩
    disjoint := by
      intro e h eh
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp hz
      obtain ⟨v, hv, hvz⟩ := Finset.mem_image.mp hz'
      have huv := hb_inj u v (route_subset e hu) (route_subset h hv) (huz.trans hvz.symm)
      subst v
      exact Finset.disjoint_left.mp (E.disjoint e h eh) hu hv }
  refine ⟨r, K, f, E', ?_, ?_, ?_⟩
  · intro e h eh u hu v hv huv
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
    obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
    subst u v
    apply induced e h eh x hx y hy
    change G.Adj (forward (backward x)) (forward (backward y)) at huv
    rwa [hf x (route_subset e hx), hf y (route_subset h hy)] at huv
  · intro e
    apply Finset.card_image_iff.mpr
    intro u hu v hv h
    exact hb_inj u v (route_subset e hu) (route_subset e hv) h
  · let iso : K ≃g G.induce S := {
      toEquiv := idx.symm
      map_rel_iff' := by intro u v; rfl }
    have h := Fintype.card_congr iso.mapEdgeSet
    simpa only [Set.fintypeCard_eq_ncard] using h


end Lax263307Proofs.HostRestriction
