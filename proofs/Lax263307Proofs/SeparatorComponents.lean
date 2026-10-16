import Lax263307.SeparatorComponents

namespace Lax263307Proofs.SeparatorComponents

open Lax263307.SeparatorComponents

/-- Connected components of the induced graph give the canonical partition. -/
noncomputable def components {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) :
    Partition G S (G.induce (↑S : Set (Fin n))ᶜ).ConnectedComponent := by
  classical
  let H := G.induce (↑S : Set (Fin n))ᶜ
  let vertices (c : H.ConnectedComponent) := (Subtype.val '' c.supp).toFinset
  exact
    { vertices := vertices
      outside := by
        intro c v hv
        obtain ⟨u, _, rfl⟩ := Set.mem_toFinset.mp hv
        exact u.property
      unique := by
        intro v hv
        let u : ↥((↑S : Set (Fin n))ᶜ) := ⟨v, hv⟩
        refine ⟨H.connectedComponentMk u, ?_, ?_⟩
        · exact Set.mem_toFinset.mpr ⟨u, rfl, rfl⟩
        · intro c hc
          obtain ⟨w, hw, he⟩ := Set.mem_toFinset.mp hc
          have hwu : w = u := Subtype.ext he
          change H.connectedComponentMk w = c at hw
          rw [hwu] at hw
          exact hw.symm
      closed := by
        intro c u v hu hv huv
        obtain ⟨u', hu', rfl⟩ := Set.mem_toFinset.mp hu
        let v' : ↥((↑S : Set (Fin n))ᶜ) := ⟨v, hv⟩
        exact Set.mem_toFinset.mpr ⟨v',
          (SimpleGraph.ConnectedComponent.mem_supp_congr_adj c
            (show H.Adj u' v' from huv)).mp hu', rfl⟩ }

end Lax263307Proofs.SeparatorComponents
