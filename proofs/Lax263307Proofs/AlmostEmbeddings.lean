import Lax263307.AlmostEmbeddings
import Lax263307Proofs.ConnectedRepresentations

namespace Lax263307Proofs.AlmostEmbeddings

open Lax263307.AlmostEmbeddings Lax263307.ConnectedRepresentations Lax228581.Treewidth

theorem carrier_mem {t n : ℕ} {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) (v : Fin t) (a : Fin n) :
    a ∈ vertexCarrier E v ↔ ∃ e : H.edgeSet, v ∈ e.val ∧ a ∈ E.route e := by
  classical
  unfold vertexCarrier
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨e, _, ha⟩
    by_cases hv : v ∈ e.val
    · exact ⟨e, hv, by simpa only [if_pos hv] using ha⟩
    · simp [hv] at ha
  · rintro ⟨e, hv, ha⟩
    exact ⟨e, Finset.mem_univ _, by simpa only [if_pos hv] using ha⟩

theorem carrier_connected {t n : ℕ} {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) (v : Fin t) (active : ¬H.IsIsolated v) :
    (G.induce (↑(vertexCarrier E v) : Set (Fin n))).Connected := by
  classical
  obtain ⟨u, huv⟩ : ∃ u, H.Adj v u := by simpa [SimpleGraph.IsIsolated] using active
  let e : H.edgeSet := ⟨s(v, u), huv⟩
  have he : v ∈ e.val := Sym2.mem_mk_left _ _
  have hroot := E.endpoints e v he
  have hroot' : E.vertexMap v ∈ vertexCarrier E v := (carrier_mem E v _).mpr ⟨e, he, hroot⟩
  let root : ↥(↑(vertexCarrier E v) : Set (Fin n)) := ⟨E.vertexMap v, hroot'⟩
  have hreach : ∀ a : ↥(↑(vertexCarrier E v) : Set (Fin n)),
      (G.induce (↑(vertexCarrier E v) : Set (Fin n))).Reachable a root := by
    intro a
    obtain ⟨f, hvf, haf⟩ := (carrier_mem E v a.val).mp a.property
    have hsubset : (↑(E.route f) : Set (Fin n)) ⊆ ↑(vertexCarrier E v) := by
      intro b hb
      exact (carrier_mem E v b).mpr ⟨f, hvf, hb⟩
    exact ((E.connected f) ⟨a.val, haf⟩ ⟨E.vertexMap v, E.endpoints f v hvf⟩).map
      (G.induceHomOfLE hsubset).toHom
  exact
    { preconnected := fun a b => (hreach a).trans (hreach b).symm
      nonempty := ⟨root⟩ }

noncomputable def representation {t n : ℕ} {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)}
    (E : AlmostEmbedding H G) (active : ∀ v, ¬H.IsIsolated v) : Representation H G where
  carrier := vertexCarrier E
  connected := fun v => carrier_connected E v (active v)
  touching := by
    intro u v huv
    let e : H.edgeSet := ⟨s(u, v), huv⟩
    have hue : u ∈ e.val := Sym2.mem_mk_left _ _
    have hve : v ∈ e.val := Sym2.mem_mk_right _ _
    exact ⟨E.vertexMap u, (carrier_mem E u _).mpr ⟨e, hue, E.endpoints e u hue⟩,
      (carrier_mem E v _).mpr ⟨e, hve, E.endpoints e u hue⟩⟩

theorem incident_endpoints {t : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    {x y : Fin t} (hxy : H.Adj x y) (f : H.edgeSet)
    (incident : ¬Disjoint ({x, y} : Finset (Fin t)) f.val.toFinset) :
    f.val.toFinset ⊆ H.neighborFinset x ∪ H.neighborFinset y := by
  obtain ⟨b, hb, hbf⟩ := Finset.not_disjoint_iff.mp incident
  have hbf' : b ∈ f.val := Sym2.mem_toFinset.mp hbf
  obtain ⟨c, hfc⟩ := Sym2.mem_iff_exists.mp hbf'
  have hbc : H.Adj b c := by
    change s(b, c) ∈ H.edgeSet
    rw [← hfc]
    exact f.property
  intro a ha
  have ha' : a = b ∨ a = c := by simpa [hfc] using ha
  have hb' : b = x ∨ b = y := by simpa using hb
  rcases hb' with rfl | rfl <;> rcases ha' with rfl | rfl
  · exact Finset.mem_union_right _ (by simpa using hxy.symm)
  · exact Finset.mem_union_left _ (by simpa using hbc)
  · exact Finset.mem_union_left _ (by simpa using hxy)
  · exact Finset.mem_union_right _ (by simpa using hbc)

theorem representation_load {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (d : ℕ)
    (hdegree : ∀ v, H.degree v ≤ d) (active : ∀ v, ¬H.IsIsolated v) (a : Fin n) :
    (users (representation E active) a).card ≤ 2 * d := by
  classical
  let L := users (representation E active) a
  by_cases hL : L = ∅
  · simp [L, hL]
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hL
    have hva : a ∈ vertexCarrier E v := (Finset.mem_filter.mp hv).2
    obtain ⟨e, _, hae⟩ := (carrier_mem E v a).mp hva
    let x := e.val.out.1
    let y := e.val.out.2
    have heq : e.val = s(x, y) := e.val.out_eq.symm
    have hxy : H.Adj x y := by
      change s(x, y) ∈ H.edgeSet
      rw [← heq]
      exact e.property
    have hsubset : L ⊆ H.neighborFinset x ∪ H.neighborFinset y := by
      intro w hw
      have hwa : a ∈ vertexCarrier E w := (Finset.mem_filter.mp hw).2
      obtain ⟨f, hwf, haf⟩ := (carrier_mem E w a).mp hwa
      have hincident : ¬Disjoint e.val.toFinset f.val.toFinset := by
        intro hdisj
        exact Finset.disjoint_left.mp (E.disjoint e f hdisj) hae haf
      have hincident' : ¬Disjoint ({x, y} : Finset (Fin t)) f.val.toFinset := by
        simpa [heq, Sym2.toFinset_mk_eq] using hincident
      exact incident_endpoints H hxy f hincident' (Sym2.mem_toFinset.mpr hwf)
    calc
      L.card ≤ (H.neighborFinset x ∪ H.neighborFinset y).card := Finset.card_le_card hsubset
      _ ≤ (H.neighborFinset x).card + (H.neighborFinset y).card := Finset.card_union_le _ _
      _ = H.degree x + H.degree y := rfl
      _ ≤ 2 * d := by have hx := hdegree x; have hy := hdegree y; omega

/--
---
conclusion: Lax263307.AlmostEmbeddings.transfer_decomposition
---
Represent a vertex by the union of its incident routes, connected through
its mapped image. At a host vertex, all routes present share an endpoint
with any one present route `xy`; their endpoints lie in `N(x) ∪ N(y)`.
Thus at most `2d` represented vertices use that host vertex. Apply the
connected-set decomposition transfer with this load bound.
-/
theorem transfer_decomposition {t n : ℕ} (H : SimpleGraph (Fin t))
    [DecidableRel H.Adj] (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G)
    (d w : ℕ) (degree_bound : ∀ v, H.degree v ≤ d)
    (no_isolates : ∀ v, ¬H.IsIsolated v)
    (D : TreeDecomposition G) (bag_bound : ∀ i, (D.bag i).card ≤ w) :
    ∃ D' : TreeDecomposition H, ∀ i, (D'.bag i).card ≤ 2 * d * w := by
  exact Lax263307.ConnectedRepresentations.transfer_decomposition H G
    (representation E no_isolates) (2 * d) w
    (representation_load H G E d degree_bound no_isolates) D bag_bound

end Lax263307Proofs.AlmostEmbeddings
