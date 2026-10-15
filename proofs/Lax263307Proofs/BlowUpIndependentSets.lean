import Lax263307.BlowUpIndependentSets
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.BlowUpIndependentSets

open Lax263307.IndependentBlowUp

/--
---
conclusion: Lax263307.BlowUpIndependentSets.lift_independent
---
The complete lift of an independent set is independent.

# Proof strategy

Copies of a common original vertex have no edge between them. For different
original vertices, independence follows from independence of the original set.

# Attribution

Bonnet–Chang, Section 6.
-/
theorem lift_independent {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ)
    (I : Finset (Fin n)) (independent : G.IsIndepSet (I : Set (Fin n))) :
    (graph G copies).IsIndepSet (lift copies I : Set (Vertex copies)) := by
  intro a ha b hb _ hab
  have haI : a.1 ∈ I := (Finset.mem_sigma.mp ha).1
  have hbI : b.1 ∈ I := (Finset.mem_sigma.mp hb).1
  change G.Adj a.1 b.1 at hab
  exact independent haI hbI hab.ne hab

/--
---
conclusion: Lax263307.BlowUpIndependentSets.project_independent
---
Projecting an independent set of copies gives an independent original set.

# Proof strategy

If two projected vertices were adjacent, their selected representatives
would be adjacent copies, contradicting independence.

# Attribution

Bonnet–Chang, Section 6.
-/
theorem project_independent {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ)
    (K : Finset (Vertex copies)) (independent : (graph G copies).IsIndepSet (K : Set (Vertex copies))) :
    G.IsIndepSet (project K : Set (Fin n)) := by
  intro u hu v hv huv hadj
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  exact independent ha hb (fun h => huv (congrArg Sigma.fst h)) hadj

/--
---
conclusion: Lax263307.BlowUpIndependentSets.lift_cardinality
---
The cardinality of a complete lift is the sum of the fibre sizes.

# Proof strategy

Use the cardinality formula for a finite dependent sum and the cardinality
of each `Fin` fibre.

# Attribution

Bonnet–Chang, Section 6.
-/
theorem lift_cardinality {n : ℕ} (copies : Fin n → ℕ) (I : Finset (Fin n)) :
    (lift copies I).card = ∑ v ∈ I, copies v := by
  simp [lift]

/--
---
conclusion: Lax263307.BlowUpIndependentSets.projection_capacity
---
The multiplicities of the projected vertices bound the number of selected copies.

# Proof strategy

Every selected copy belongs to the complete lift of the projection.
Compare cardinalities and use the lift-cardinality statement.

# Attribution

Bonnet–Chang, Section 6.
-/
theorem projection_capacity {n : ℕ} (copies : Fin n → ℕ) (K : Finset (Vertex copies)) :
    K.card ≤ ∑ v ∈ project K, copies v := by
  have hsub : K ⊆ lift copies (project K) := by
    intro a ha
    simp only [lift, Finset.mem_sigma, Finset.mem_univ, and_true]
    exact Finset.mem_image_of_mem _ ha
  exact (Finset.card_le_card hsub).trans_eq
    (Lax263307.BlowUpIndependentSets.lift_cardinality copies (project K))


end Lax263307Proofs.BlowUpIndependentSets
