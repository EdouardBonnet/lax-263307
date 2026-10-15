import Lax263307.WeightedAlgorithm
import Mathlib.Tactic

namespace Lax263307Proofs.WeightedAlgorithm

open Lax263307.WeightedAlgorithm Lax263307.WeightRounding Lax263307.IndependentBlowUp
open Lax263307.PositiveWeights Lax263307.WeightedIndependentSet
open Lax263307.GraphClasses Lax263307.BlowUpClasses Lax263307.EdgeSublinearSeparators

theorem relabel_approximation {n : ℕ} (G : SimpleGraph (Fin n)) (copies : Fin n → ℕ)
    (δ : ℚ) (I : Finset (Fin (∑ v, copies v)))
    (hI : IsApproximation (numbered G copies) (fun _ => 1) δ I) :
    IsCardinalityApproximation G copies δ (I.image (labeling copies)) := by
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    exact hI.1 hi hj (fun hij => huv (congrArg (labeling copies) hij))
  · intro J hJ
    let J' := J.image (labeling copies).symm
    have hJ' : (numbered G copies).IsIndepSet (J' : Set (Fin (∑ v, copies v))) := by
      intro i hi j hj hij
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
      have huv : u ≠ v := fun he => hij (congrArg (labeling copies).symm he)
      simpa only [numbered, SimpleGraph.comap_adj, Equiv.apply_symm_apply] using hJ hu hv huv
    have hh := hI.2 J' hJ'
    simp only [weight, Finset.sum_const, nsmul_eq_mul, mul_one] at hh
    rw [Finset.card_image_of_injective _ (labeling copies).injective]
    simpa only [J', Finset.card_image_of_injective _ (labeling copies).symm.injective] using hh


end Lax263307Proofs.WeightedAlgorithm
