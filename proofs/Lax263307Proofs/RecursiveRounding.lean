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

/--
---
conclusion: Lax263307.RecursiveRounding.round_or_cut
---
If a part's cost exceeds its certified bound, Lemma 13 supplies the cut.
Otherwise sum the recursive size guarantees, replace each bound by the
corresponding part cost, and use the separator's lightness to retain one
additional factor of `1-δ`.

# Attribution

Bonnet–Chang, equation (24) in Lemma 14.
-/
theorem round_or_cut {n r : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (k h : ℕ) (δ : ℝ)
    (_δ_nonnegative : 0 ≤ δ) (δ_small : δ ≤ 1)
    (y : MomentVector n r) (A S : Finset (Fin n)) (P : Partition G S ι)
    (size : A.card ≤ r) (positive : 0 < value y A)
    (mass : (∑ v, conditioned y A v) = k)
    (light : ∑ v ∈ S, conditioned y A v ≤ δ * k)
    (I : ι → Finset (Fin n)) (u : ι → ℕ)
    (inside : ∀ i, I i ⊆ P.vertices i)
    (independent : ∀ i, G.IsIndepSet (I i : Set (Fin n)))
    (bounds : ∀ i, IsIndependenceBound G (P.vertices i) (u i))
    (approximation : ∀ i, (1 - δ) ^ h * (u i : ℝ) ≤ (I i).card) :
    (G.IsIndepSet (combine I : Set (Fin n)) ∧
      (1 - δ) ^ (h + 1) * (k : ℝ) ≤ (combine I).card) ∨
    ∃ i, (∀ z ∈ independentSetHull G k r,
      ∑ v ∈ P.vertices i, value z (insert v A) ≤ (u i : ℝ) * value z A) ∧
      (u i : ℝ) * value y A < ∑ v ∈ P.vertices i, value y (insert v A) := by
  classical
  by_cases hcut : ∃ i, (u i : ℝ) < ∑ v ∈ P.vertices i, conditioned y A v
  · obtain ⟨i, hi⟩ := hcut
    right
    exact ⟨i, fun z hz => Lax263307.ComponentCuts.valid_cut G k r
      (P.vertices i) (u i) (bounds i) A size z hz,
      (Lax263307.ComponentCuts.violation_iff y A (P.vertices i) (u i) positive).mp hi⟩
  · have hcost : ∀ i, (∑ v ∈ P.vertices i, conditioned y A v) ≤ (u i : ℝ) := by
      simpa using hcut
    obtain ⟨hI, hcard⟩ := Lax263307.RecursiveRounding.combine_independent
      G S P I inside independent
    left
    refine ⟨hI, ?_⟩
    have hfactor : 0 ≤ (1 - δ) ^ h := pow_nonneg (by linarith) h
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => approximation i)
    have hsumcost := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcost i)
    rw [parts_sum P, mass] at hsumcost
    have hremaining : (1 - δ) * (k : ℝ) ≤ ∑ i, (u i : ℝ) := by linarith
    calc
      (1 - δ) ^ (h + 1) * (k : ℝ) = (1 - δ) ^ h * ((1 - δ) * k) := by
        rw [pow_succ]; ring
      _ ≤ (1 - δ) ^ h * ∑ i, (u i : ℝ) := mul_le_mul_of_nonneg_left hremaining hfactor
      _ ≤ ∑ i, ((I i).card : ℝ) := by simpa only [Finset.mul_sum] using hsum
      _ = (combine I).card := by exact_mod_cast hcard.symm

end Lax263307Proofs.RecursiveRounding
