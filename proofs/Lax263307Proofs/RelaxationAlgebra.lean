import Lax263307.LinearRelaxation
import Mathlib.Tactic

namespace Lax263307Proofs.RelaxationAlgebra

open Lax263307.LinearRelaxation

theorem value_of_size {n r : ℕ} (y : MomentVector n r)
    (A : Finset (Fin n)) (hA : A.card ≤ r + 2) : value y A = y ⟨A, hA⟩ := by
  simp [value, hA]

theorem value_combination {n r : ℕ} (y z : MomentVector n r)
    (a b : ℝ) (A : Finset (Fin n)) :
    value (a • y + b • z) A = a * value y A + b * value z A := by
  by_cases hA : A.card ≤ r + 2 <;> simp [value, hA]

theorem indicator_value {n r : ℕ} (I A : Finset (Fin n))
    (hA : A.card ≤ r + 2) :
    value (indicator r I) A = if A ⊆ I then 1 else 0 := by
  simp [value, indicator, hA]

theorem insert_size {n r : ℕ} (A : Finset (Fin n))
    (hA : A.card ≤ r + 1) (v : Fin n) : (insert v A).card ≤ r + 2 := by
  have := Finset.card_insert_le v A
  omega

theorem indicator_sum {n r : ℕ} (I A C : Finset (Fin n))
    (hA : A.card ≤ r + 1) :
    (∑ v ∈ C, value (indicator r I) (insert v A)) =
      if A ⊆ I then ((C ∩ I).card : ℝ) else 0 := by
  simp_rw [indicator_value I _ (insert_size A hA _), Finset.insert_subset_iff]
  by_cases hAI : A ⊆ I
  · simp [hAI]
  · simp [hAI]

theorem independent_subset {n : ℕ} (G : SimpleGraph (Fin n))
    {I J : Finset (Fin n)} (hI : G.IsIndepSet (I : Set (Fin n))) (hJI : J ⊆ I) :
    G.IsIndepSet (J : Set (Fin n)) :=
  hI.mono (by simpa using hJI)

end Lax263307Proofs.RelaxationAlgebra
