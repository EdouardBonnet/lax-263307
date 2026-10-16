import Lax263307.InducedRouteEdges
import Lax263307Proofs.AlmostEmbeddings

namespace Lax263307Proofs.InducedRouteEdges

open Lax263307.AlmostEmbeddings Lax263307.InducedRouteEdges

noncomputable def incidentEdges {t : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (e : H.edgeSet) :
    Finset H.edgeSet := by
  classical
  exact Finset.univ.filter fun f => ¬Disjoint e.val.toFinset f.val.toFinset

theorem incidentEdges_card {t : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (e : H.edgeSet) (d : ℕ) (hdegree : ∀ v, H.degree v ≤ d) :
    (incidentEdges H e).card ≤ 2 * d := by
  classical
  let x := e.val.out.1
  let y := e.val.out.2
  have heq : e.val = s(x, y) := e.val.out_eq.symm
  have hsub : (incidentEdges H e).image Subtype.val ⊆
      H.incidenceFinset x ∪ H.incidenceFinset y := by
    intro q hq
    obtain ⟨f, hf, hfq⟩ := Finset.mem_image.mp hq
    subst q
    obtain ⟨b, hbe, hbf⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hf).2
    have hb : b = x ∨ b = y := by simpa [heq] using hbe
    have hbf' := Sym2.mem_toFinset.mp hbf
    rcases hb with rfl | rfl
    · exact Finset.mem_union_left _ ((H.mem_incidenceFinset x f.val).mpr ⟨f.property, hbf'⟩)
    · exact Finset.mem_union_right _ ((H.mem_incidenceFinset y f.val).mpr ⟨f.property, hbf'⟩)
  calc
    (incidentEdges H e).card = ((incidentEdges H e).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (H.incidenceFinset x ∪ H.incidenceFinset y).card := Finset.card_le_card hsub
    _ ≤ (H.incidenceFinset x).card + (H.incidenceFinset y).card := Finset.card_union_le _ _
    _ = H.degree x + H.degree y := by rw [H.card_incidenceFinset_eq_degree, H.card_incidenceFinset_eq_degree]
    _ ≤ 2 * d := by have hx := hdegree x; have hy := hdegree y; omega

theorem routeUnion_card {t n : ℕ} {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)}
    [DecidableRel H.Adj]
    (E : AlmostEmbedding H G) (L : ℕ) (hlength : ∀ e, (E.route e).card ≤ L) :
    (routeUnion E).card ≤ H.edgeSet.ncard * L := by
  classical
  calc
    (routeUnion E).card ≤ ∑ e, (E.route e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e : H.edgeSet, L := Finset.sum_le_sum fun e _ => hlength e
    _ = Fintype.card H.edgeSet * L := by simp
    _ = H.edgeSet.ncard * L := by rw [Set.fintypeCard_eq_ncard]

theorem routeUnion_degree {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (d L : ℕ)
    (induced : IsInduced E) (hdegree : ∀ v, H.degree v ≤ d)
    (hlength : ∀ e, (E.route e).card ≤ L)
    (a : ↥(↑(routeUnion E) : Set (Fin n))) :
    (by classical exact (G.induce (↑(routeUnion E) : Set (Fin n))).degree a) ≤ 2 * d * L := by
  classical
  let F := G.induce (↑(routeUnion E) : Set (Fin n))
  obtain ⟨e, _, hae⟩ := Finset.mem_biUnion.mp a.property
  let B := (incidentEdges H e).biUnion E.route
  have hsub : (F.neighborFinset a).image Subtype.val ⊆ B := by
    intro b hb
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb
    have hab : F.Adj a b := by simpa using hb
    obtain ⟨f, _, hbf⟩ := Finset.mem_biUnion.mp b.property
    have hinc : ¬Disjoint e.val.toFinset f.val.toFinset := by
      intro hdisj
      exact induced e f hdisj a.val hae b.val hbf hab
    exact Finset.mem_biUnion.mpr ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc⟩, hbf⟩
  calc
    F.degree a = ((F.neighborFinset a).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ B.card := Finset.card_le_card hsub
    _ ≤ ∑ f ∈ incidentEdges H e, (E.route f).card := Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ incidentEdges H e, L := Finset.sum_le_sum fun f _ => hlength f
    _ = (incidentEdges H e).card * L := by simp
    _ ≤ 2 * d * L := Nat.mul_le_mul_right L (incidentEdges_card H e d hdegree)

/--
---
conclusion: Lax263307.InducedRouteEdges.edge_bound
---
For each host vertex choose a route using it. All of its neighbors in the
route union lie on routes incident to this chosen source edge, since the
almost-embedding is induced. There are at most `2d` such routes and each has
at most `L` vertices. Combine this degree bound with the route-union order
bound and the degree-sum formula.
-/
theorem edge_bound {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (d L : ℕ)
    (induced : IsInduced E) (degree_bound : ∀ v, H.degree v ≤ d)
    (length_bound : ∀ e, (E.route e).card ≤ L) :
    (G.induce (↑(routeUnion E) : Set (Fin n))).edgeSet.ncard ≤
      d * H.edgeSet.ncard * L ^ 2 := by
  classical
  let F := G.induce (↑(routeUnion E) : Set (Fin n))
  change F.edgeSet.ncard ≤ d * H.edgeSet.ncard * L ^ 2
  have hsum : (∑ a, F.degree a) ≤ 2 * d * L * (routeUnion E).card := by
    calc
      (∑ a, F.degree a) ≤ ∑ _a : ↥(↑(routeUnion E) : Set (Fin n)), 2 * d * L :=
        Finset.sum_le_sum fun a _ => routeUnion_degree H G E d L induced degree_bound length_bound a
      _ = 2 * d * L * (routeUnion E).card := by simp [Nat.mul_comm]
  have horder := routeUnion_card E L length_bound
  have hcount : (∑ a, F.degree a) = 2 * F.edgeSet.ncard := by
    rw [F.sum_degrees_eq_twice_card_edges, SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]
  have hproduct := Nat.mul_le_mul_left (2 * d * L) horder
  have hbound : 2 * F.edgeSet.ncard ≤ 2 * (d * H.edgeSet.ncard * L ^ 2) := by
    calc
      2 * F.edgeSet.ncard ≤ 2 * d * L * (routeUnion E).card := by simpa only [hcount] using hsum
      _ ≤ 2 * d * L * (H.edgeSet.ncard * L) := hproduct
      _ = 2 * (d * H.edgeSet.ncard * L ^ 2) := by ring
  omega

end Lax263307Proofs.InducedRouteEdges
