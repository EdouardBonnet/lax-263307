import Lax263307.RecursiveRounding
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.RecursiveRounding

open Lax263307.LinearRelaxation Lax263307.SeparatorComponents

theorem parts_disjoint {n : ℕ} {ι : Type} [Fintype ι]
    {G : SimpleGraph (Fin n)} {S : Finset (Fin n)} (P : Partition G S ι) :
    (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint P.vertices := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨c, _, hc⟩ := P.unique v (P.outside i v hvi)
  exact hij ((hc i hvi).trans (hc j hvj).symm)

theorem parts_cover {n : ℕ} {ι : Type} [Fintype ι]
    {G : SimpleGraph (Fin n)} {S : Finset (Fin n)} (P : Partition G S ι) :
    combine P.vertices = Finset.univ \ S := by
  classical
  ext v
  simp only [combine, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨i, hi⟩
    exact P.outside i v hi
  · intro hv
    obtain ⟨i, hi, _⟩ := P.unique v hv
    exact ⟨i, hi⟩

theorem parts_sum {n : ℕ} {ι : Type} [Fintype ι]
    {G : SimpleGraph (Fin n)} {S : Finset (Fin n)} (P : Partition G S ι)
    (x : Fin n → ℝ) :
    (∑ i, ∑ v ∈ P.vertices i, x v) = (∑ v, x v) - ∑ v ∈ S, x v := by
  classical
  rw [← Finset.sum_biUnion (parts_disjoint P)]
  change (∑ v ∈ combine P.vertices, x v) = _
  rw [parts_cover P]
  have hsplit := Finset.sum_sdiff (f := x) (Finset.subset_univ S)
  linarith

/--
---
conclusion: Lax263307.RecursiveRounding.combine_independent
---
An edge cannot connect different parts of the partition. The selected sets
inherit the disjointness of those parts, so their union's cardinality is the
sum of their cardinalities.
-/
theorem combine_independent {n : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (P : Partition G S ι)
    (I : ι → Finset (Fin n)) (inside : ∀ i, I i ⊆ P.vertices i)
    (independent : ∀ i, G.IsIndepSet (I i : Set (Fin n))) :
    G.IsIndepSet (combine I : Set (Fin n)) ∧ (combine I).card = ∑ i, (I i).card := by
  classical
  have hdisj : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint I := by
    intro i hi j hj hne
    exact (parts_disjoint P hi hj hne).mono (inside i) (inside j)
  refine ⟨?_, Finset.card_biUnion hdisj⟩
  intro a ha b hb hab hadj
  obtain ⟨i, _, hai⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨j, _, hbj⟩ := Finset.mem_biUnion.mp hb
  have hai' := inside i hai
  have hbj' := inside j hbj
  have hbi := P.closed i a b hai' (P.outside j b hbj') hadj
  obtain ⟨c, _, hc⟩ := P.unique b (P.outside j b hbj')
  have hij : i = j := (hc i hbi).trans (hc j hbj').symm
  subst j
  exact independent i hai hbj hab hadj


end Lax263307Proofs.RecursiveRounding
