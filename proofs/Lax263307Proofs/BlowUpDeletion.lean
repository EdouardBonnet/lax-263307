import Lax263307.BlowUpDeletion
import Lax263307Proofs.TreeExtensions

namespace Lax263307Proofs.BlowUpDeletion

open Lax263307.IndependentBlowUp Lax263307.BlowUpDeletion Lax228581.Treewidth
open TreeExtensions

/--
---
conclusion: Lax263307.BlowUpDeletion.high_degree_card
---
Sum the degree lower bounds on the deleted vertices and apply the degree-sum
formula to the whole blow-up.
-/
theorem high_degree_card {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s : ℕ) :
    s * (highDegree G copies s).card ≤ 2 * (graph G copies).edgeSet.ncard := by
  classical
  let H := graph G copies
  calc
    s * (highDegree G copies s).card = ∑ _v ∈ highDegree G copies s, s := by
      simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ highDegree G copies s, H.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.le_of_lt (Finset.mem_filter.mp hv).2
    _ ≤ ∑ v, H.degree v := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
    _ = 2 * H.edgeSet.ncard := by
      rw [SimpleGraph.edgeFinset_card, Set.fintypeCard_eq_ncard]

theorem fibre_le_neighbor_degree {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (v : Fin n) (b : Vertex copies) (adj : G.Adj b.1 v) :
    copies v ≤ (by classical exact (graph G copies).degree b) := by
  classical
  let H := graph G copies
  calc
    copies v = (lift copies {v}).card := by
      rw [Lax263307.BlowUpIndependentSets.lift_cardinality]
      simp
    _ ≤ (H.neighborFinset b).card := Finset.card_le_card (by
      intro a ha
      have : a.1 = v := by simpa [lift] using ha
      have hadj : H.Adj b a := by change G.Adj b.1 a.1; simpa [this] using adj
      simpa using hadj)
    _ = H.degree b := SimpleGraph.card_neighborFinset_eq_degree _ _

theorem active_fibre_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s : ℕ)
    (a : ↥((↑(highDegree G copies s) : Set (Vertex copies))ᶜ))
    (active : ¬((graph G copies).induce
      (↑(highDegree G copies s) : Set (Vertex copies))ᶜ).IsIsolated a) :
    copies a.val.1 ≤ s := by
  classical
  obtain ⟨b, hab⟩ : ∃ b, ((graph G copies).induce
      (↑(highDegree G copies s) : Set (Vertex copies))ᶜ).Adj a b := by
    simpa [SimpleGraph.IsIsolated] using active
  have hb : (graph G copies).degree b.val ≤ s := by
    have := b.property
    simpa [highDegree] using this
  exact (fibre_le_neighbor_degree G copies a.val.1 b.val hab.symm).trans hb

/--
---
conclusion: Lax263307.BlowUpDeletion.deletion_decomposition
---
Every nonisolated survivor belongs to a fibre of size at most `s`: a surviving
neighbor has degree at least that fibre size. Embed these survivors into the
uniform `s`-fold blow-up, pull back its lifted decomposition, insert the
isolated survivors in singleton bags, and add the removed vertices to every
bag.

# Attribution

Bonnet–Chang, proof of Lemma 16.
-/
theorem deletion_decomposition {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (s w : ℕ) (width : HasTreewidthAtMost G w) :
    ∃ D : TreeDecomposition (graph G copies),
      ∀ i, (D.bag i).card ≤ (highDegree G copies s).card + max 1 (s * (w + 1)) := by
  classical
  let X := highDegree G copies s
  let H := (graph G copies).induce (↑X : Set (Vertex copies))ᶜ
  let S : Set ↥((↑X : Set (Vertex copies))ᶜ) := {a | ¬H.IsIsolated a}
  let f : H.induce S ↪g graph G (fun _ => s) :=
    { toFun := fun a => ⟨a.val.val.1, ⟨a.val.val.2.val,
          a.val.val.2.isLt.trans_le (active_fibre_bound G copies s a.val a.property)⟩⟩
      inj' := by
        intro a b he
        have hfirst := congrArg Sigma.fst he
        cases a with
        | mk a ha =>
          cases b with
          | mk b hb =>
            cases a with
            | mk a ha' =>
              cases b with
              | mk b hb' =>
                cases a with
                | mk av ai =>
                  cases b with
                  | mk bv bi =>
                    dsimp at hfirst
                    subst bv
                    have hidx : ai = bi := Fin.ext (congrArg (fun a => a.2.val) he)
                    subst bi
                    rfl
      map_rel_iff' := by intro a b; rfl }
  obtain ⟨D, hD⟩ := Lax263307.BlowUpDecompositions.bounded_blowup_decomposition
    G (fun _ => s) s w (fun _ => le_rfl) width
  let D₀ := pullback f D
  have hD₀ : ∀ i, (D₀.bag i).card ≤ max 1 (s * (w + 1)) :=
    fun i => (pullback_card f D i).trans ((hD i).trans (le_max_right _ _))
  have hisolated : ∀ a, a ∉ S → H.IsIsolated a := by
    intro a ha
    exact Classical.not_not.mp ha
  let D₁ := extendIsolated S hisolated D₀
  have hD₁ : ∀ i, (D₁.bag i).card ≤ max 1 (s * (w + 1)) :=
    extendIsolated_card S hisolated D₀ _ (le_max_left _ _) hD₀
  exact ⟨restoreDeleted X D₁, restoreDeleted_card X D₁ _ hD₁⟩

/--
---
conclusion: Lax263307.BlowUpDeletion.power_bound
---
Choose `s` to be the ceiling of `(m+1)^((1-b)/2)`. The deletion term and
the lifted-bag term then both have exponent `(1+b)/2`, with the additional
one accounting for isolated vertices.

# Attribution

Bonnet–Chang, the threshold optimization in Lemma 16.
-/
theorem power_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (copies : Fin n → ℕ) (w : ℕ) (b c : ℝ) (hb : 0 ≤ b) (hb₁ : b < 1)
    (_hc : 0 < c) (width : HasTreewidthAtMost G w)
    (width_bound : (w + 1 : ℕ) ≤
      c * Real.rpow ((graph G copies).edgeSet.ncard + 1) b) :
    ∃ D : TreeDecomposition (graph G copies), ∀ i,
      ((D.bag i).card : ℝ) ≤ (3 + 2 * c) *
        Real.rpow ((graph G copies).edgeSet.ncard + 1) ((1 + b) / 2) := by
  classical
  let m := (graph G copies).edgeSet.ncard
  let M : ℝ := (m : ℝ) + 1
  let α := (1 - b) / 2
  let β := (1 + b) / 2
  let q := Real.rpow M α
  let t := Real.rpow M β
  let s := Nat.ceil q
  have hM : 1 ≤ M := by dsimp [M]; exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hq : 1 ≤ q := Real.one_le_rpow hM hα
  have ht : 1 ≤ t := Real.one_le_rpow hM hβ
  have hqs : q ≤ (s : ℝ) := Nat.le_ceil q
  have hs : (s : ℝ) ≤ 2 * q := by
    have hceil := Nat.ceil_le_floor_add_one q
    have hfloor := Nat.floor_le (show 0 ≤ q by linarith)
    have hcast : (s : ℝ) ≤ (Nat.floor q : ℝ) + 1 := by exact_mod_cast hceil
    linarith
  have hqt : q * t = M := by
    dsimp [q, t]
    rw [← Real.rpow_add hMpos]
    have : α + β = 1 := by dsimp [α, β]; ring
    rw [this, Real.rpow_one]
  have hqb : q * Real.rpow M b = t := by
    dsimp [q, t]
    rw [← Real.rpow_add hMpos]
    have : α + b = β := by dsimp [α, β]; ring
    rw [this]
  have hhigh : ((highDegree G copies s).card : ℝ) ≤ 2 * t := by
    have hdegree : (s : ℝ) * (highDegree G copies s).card ≤ 2 * (m : ℝ) := by
      exact_mod_cast Lax263307.BlowUpDeletion.high_degree_card G copies s
    have hX : 0 ≤ ((highDegree G copies s).card : ℝ) := by positivity
    have hqX : q * (highDegree G copies s).card ≤ (s : ℝ) * (highDegree G copies s).card :=
      mul_le_mul_of_nonneg_right hqs hX
    have hmul : q * (highDegree G copies s).card ≤ q * (2 * t) := by
      calc
        q * (highDegree G copies s).card ≤ 2 * (m : ℝ) := hqX.trans hdegree
        _ ≤ 2 * M := by dsimp [M]; linarith
        _ = q * (2 * t) := by rw [mul_left_comm, hqt]
    exact (mul_le_mul_iff_right₀ (show 0 < q by linarith)).mp hmul
  have hlift : (s : ℝ) * (w + 1 : ℕ) ≤ 2 * c * t := by
    calc
      (s : ℝ) * (w + 1 : ℕ) ≤ (2 * q) * (c * Real.rpow M b) :=
        mul_le_mul hs width_bound (by positivity) (by positivity)
      _ = 2 * c * t := by rw [← hqb]; ring
  obtain ⟨D, hD⟩ := Lax263307.BlowUpDeletion.deletion_decomposition G copies s w width
  refine ⟨D, ?_⟩
  intro i
  have hbag : ((D.bag i).card : ℝ) ≤ (highDegree G copies s).card +
      max 1 ((s : ℝ) * (w + 1 : ℕ)) := by exact_mod_cast hD i
  have hmax : max 1 ((s : ℝ) * (w + 1 : ℕ)) ≤ 1 + (s : ℝ) * (w + 1 : ℕ) :=
    max_le (le_add_of_nonneg_right (by positivity)) (by linarith)
  change ((D.bag i).card : ℝ) ≤ (3 + 2 * c) * t
  nlinarith

end Lax263307Proofs.BlowUpDeletion
