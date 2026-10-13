import Lax263307.LinearRelaxation
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
---
title: The components left by deleting a separator
type: definition
---
Deleting a vertex set $S$ partitions the remaining vertices into connected
components. Every undeleted vertex belongs to exactly one part, and every
edge with undeleted endpoints has both endpoints in one part. These are the
properties used to combine the recursive independent sets.

# Formalization notes

`Partition` also permits grouping connected components together. The canonical
`components` construction uses precisely the connected components of $G-S$.
The vertex sets of the parts are finite sets in the original vertex type.
-/

namespace Lax263307.SeparatorComponents

/-- A partition of the undeleted vertices, closed under undeleted edges. -/
structure Partition {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (ι : Type) where
  /-- The original vertices in each part. -/
  vertices : ι → Finset (Fin n)
  /-- Parts exclude the deleted vertices. -/
  outside : ∀ i v, v ∈ vertices i → v ∉ S
  /-- Every undeleted vertex belongs to exactly one part. -/
  unique : ∀ v, v ∉ S → ∃! i, v ∈ vertices i
  /-- No undeleted edge leaves a part. -/
  closed : ∀ i u v, u ∈ vertices i → v ∉ S → G.Adj u v → v ∈ vertices i

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

/-- The recursive answer is the union of the answers on the parts. -/
def combine {n : ℕ} {ι : Type} [Fintype ι] (I : ι → Finset (Fin n)) :
    Finset (Fin n) := Finset.univ.biUnion I

end Lax263307.SeparatorComponents
