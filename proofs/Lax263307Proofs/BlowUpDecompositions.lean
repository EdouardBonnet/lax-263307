import Lax263307.BlowUpDecompositions

namespace Lax263307Proofs.BlowUpDecompositions

open Lax263307.IndependentBlowUp Lax228581.Treewidth

/-- Keep the original decomposition tree and lift every bag to all its copies. -/
def liftDecomposition {n : ℕ} {G : SimpleGraph (Fin n)} (copies : Fin n → ℕ)
    (D : TreeDecomposition G) : TreeDecomposition (graph G copies) where
  Node := D.Node
  nodeFintype := D.nodeFintype
  tree := D.tree
  isTree := D.isTree
  bag i := lift copies (D.bag i)
  vertex_mem_bag a := by
    obtain ⟨i, hi⟩ := D.vertex_mem_bag a.1
    exact ⟨i, by simp [lift, hi]⟩
  edge_mem_bag := by
    intro a b hab
    obtain ⟨i, ha, hb⟩ := D.edge_mem_bag hab
    exact ⟨i, by simp [lift, ha], by simp [lift, hb]⟩
  bag_indices_connected a := by
    have hset : {i : D.Node | a ∈ lift copies (D.bag i)} =
        {i : D.Node | a.1 ∈ D.bag i} := by
      ext i
      simp [lift]
    rw [hset]
    exact D.bag_indices_connected a.1

/--
---
conclusion: Lax263307.BlowUpDecompositions.bounded_blowup_decomposition
---
The lifted tree decomposition has bags bounded by the original bag size
times the largest fibre size.

# Proof strategy

Construct the lifted decomposition on the original tree. A copy occurs
at exactly the nodes where its original vertex occurs, preserving connected
bag indices. Count each lifted bag with the lift-cardinality statement
and bound all fibre sizes by `s`.
-/
theorem bounded_blowup_decomposition {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s w : ℕ) (bounded : ∀ v, copies v ≤ s)
    (width : HasTreewidthAtMost G w) :
    ∃ D : TreeDecomposition (graph G copies), ∀ i, (D.bag i).card ≤ s * (w + 1) := by
  obtain ⟨D, hD⟩ := width
  refine ⟨liftDecomposition copies D, ?_⟩
  intro i
  change (lift copies (D.bag i)).card ≤ s * (w + 1)
  rw [Lax263307.BlowUpIndependentSets.lift_cardinality]
  calc
    (∑ v ∈ D.bag i, copies v) ≤ ∑ _v ∈ D.bag i, s :=
      Finset.sum_le_sum fun v _ => bounded v
    _ = s * (D.bag i).card := by simp [Nat.mul_comm]
    _ ≤ s * (w + 1) := Nat.mul_le_mul_left s (hD i)

end Lax263307Proofs.BlowUpDecompositions
