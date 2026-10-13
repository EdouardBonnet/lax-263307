import Lax263307.ConnectedRepresentations
import Lax263307Proofs.ConnectedBags

namespace Lax263307Proofs.ConnectedRepresentations

open Lax263307.ConnectedRepresentations Lax263307.ConnectedBags Lax228581.Treewidth

/-- Replace every host bag by all represented vertices whose carriers meet it. -/
def representationBag {t n : ℕ} {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)}
    (R : Representation H G) (bag : Finset (Fin n)) : Finset (Fin t) :=
  bag.biUnion (users R)

theorem representationBag_mem {t n : ℕ} {H : SimpleGraph (Fin t)}
    {G : SimpleGraph (Fin n)} (R : Representation H G) (bag : Finset (Fin n))
    (v : Fin t) : v ∈ representationBag R bag ↔ ∃ a ∈ R.carrier v, a ∈ bag := by
  simp only [representationBag, users, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor <;> rintro ⟨a, ha, hb⟩ <;> exact ⟨a, hb, ha⟩

def transfer {t n : ℕ} {H : SimpleGraph (Fin t)} {G : SimpleGraph (Fin n)}
    (R : Representation H G) (D : TreeDecomposition G) : TreeDecomposition H where
  Node := D.Node
  nodeFintype := D.nodeFintype
  tree := D.tree
  isTree := D.isTree
  bag i := representationBag R (D.bag i)
  vertex_mem_bag v := by
    obtain ⟨a⟩ := (R.connected v).nonempty
    obtain ⟨i, hi⟩ := D.vertex_mem_bag a.val
    exact ⟨i, (representationBag_mem R (D.bag i) v).mpr ⟨a.val, a.property, hi⟩⟩
  edge_mem_bag := by
    intro u v huv
    obtain ⟨a, hau, hav⟩ := R.touching u v huv
    obtain ⟨i, hi⟩ := D.vertex_mem_bag a
    exact ⟨i, (representationBag_mem R (D.bag i) u).mpr ⟨a, hau, hi⟩,
      (representationBag_mem R (D.bag i) v).mpr ⟨a, hav, hi⟩⟩
  bag_indices_connected v := by
    have hset : {i | v ∈ representationBag R (D.bag i)} = meetingNodes D (R.carrier v) := by
      ext i
      exact representationBag_mem R (D.bag i) v
    rw [hset]
    exact Lax263307.ConnectedBags.meeting_connected G D (R.carrier v) (R.connected v)

/--
---
conclusion: Lax263307.ConnectedRepresentations.transfer_decomposition
---
Keep the original tree and replace each bag by all represented vertices
whose carriers meet it. Connected carriers preserve connected bag indices;
touching carriers ensure edge coverage. Sum the load bound over each original
bag to obtain the new bag-size bound.

# Attribution

The transfer construction in Bonnet–Chang, Lemma 9.
-/
theorem transfer_decomposition {t n : ℕ} (H : SimpleGraph (Fin t))
    (G : SimpleGraph (Fin n)) (R : Representation H G)
    (B w : ℕ) (load_bound : ∀ a, (users R a).card ≤ B)
    (D : TreeDecomposition G) (bag_bound : ∀ i, (D.bag i).card ≤ w) :
    ∃ D' : TreeDecomposition H, ∀ i, (D'.bag i).card ≤ B * w := by
  refine ⟨transfer R D, ?_⟩
  intro i
  calc
    (representationBag R (D.bag i)).card ≤ ∑ a ∈ D.bag i, (users R a).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ D.bag i, B := Finset.sum_le_sum fun a _ => load_bound a
    _ = B * (D.bag i).card := by simp [Nat.mul_comm]
    _ ≤ B * w := Nat.mul_le_mul_left B (bag_bound i)

end Lax263307Proofs.ConnectedRepresentations
