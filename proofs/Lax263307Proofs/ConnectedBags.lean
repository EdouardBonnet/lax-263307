import Lax263307.ConnectedBags
import Mathlib.Tactic

namespace Lax263307Proofs.ConnectedBags

open Lax263307.ConnectedBags Lax228581.Treewidth

theorem vertex_meeting_reachable {n : ℕ} {G : SimpleGraph (Fin n)}
    (D : TreeDecomposition G) (U : Finset (Fin n)) (v : Fin n) (hv : v ∈ U)
    (i j : ↥(meetingNodes D U)) (hi : v ∈ D.bag i.val) (hj : v ∈ D.bag j.val) :
    (D.tree.induce (meetingNodes D U)).Reachable i j := by
  let f := D.tree.induceHomOfLE
    (show {k | v ∈ D.bag k} ⊆ meetingNodes D U from fun k hk => ⟨v, hv, hk⟩)
  exact ((D.bag_indices_connected v) ⟨i.val, hi⟩ ⟨j.val, hj⟩).map f.toHom

theorem walk_meeting_reachable {n : ℕ} {G : SimpleGraph (Fin n)}
    (D : TreeDecomposition G) (U : Finset (Fin n))
    {u v : ↥(↑U : Set (Fin n))} (p : (G.induce (↑U : Set (Fin n))).Walk u v)
    (i j : ↥(meetingNodes D U)) (hi : u.val ∈ D.bag i.val) (hj : v.val ∈ D.bag j.val) :
    (D.tree.induce (meetingNodes D U)).Reachable i j := by
  induction p generalizing i with
  | @nil u => exact vertex_meeting_reachable D U u.val u.property i j hi hj
  | @cons u a v huv p ih =>
    obtain ⟨b, hbu, hba⟩ := D.edge_mem_bag huv
    let b' : ↥(meetingNodes D U) := ⟨b, u.val, u.property, hbu⟩
    exact (vertex_meeting_reachable D U u.val u.property i b' hi hbu).trans
      (ih b' hba hj)

/--
---
conclusion: Lax263307.ConnectedBags.meeting_connected
---
Choose witnesses in the two bags and a walk joining them inside the connected
vertex set. For each edge of that walk, use a bag containing its endpoints.
The connected bag indices for each vertex join these edge bags into a walk
between the original nodes, entirely inside the nodes meeting the vertex set.

# Attribution

Bonnet–Chang, connected-bag observation in Lemma 9.
-/
theorem meeting_connected {n : ℕ} (G : SimpleGraph (Fin n))
    (D : TreeDecomposition G) (U : Finset (Fin n))
    (connected : (G.induce (↑U : Set (Fin n))).Connected) :
    (D.tree.induce (meetingNodes D U)).Connected := by
  obtain ⟨u⟩ := connected.nonempty
  obtain ⟨b, hb⟩ := D.vertex_mem_bag u.val
  have hnonempty : Nonempty ↥(meetingNodes D U) := ⟨⟨b, u.val, u.property, hb⟩⟩
  refine { preconnected := ?_, nonempty := hnonempty }
  intro i j
  obtain ⟨a, ha, hai⟩ := i.property
  obtain ⟨b, hb, hbj⟩ := j.property
  obtain ⟨p⟩ := connected ⟨a, ha⟩ ⟨b, hb⟩
  exact walk_meeting_reachable D U p i j hai hbj

end Lax263307Proofs.ConnectedBags
