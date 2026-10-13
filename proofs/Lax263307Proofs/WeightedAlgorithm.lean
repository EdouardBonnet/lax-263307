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

/--
---
conclusion: Lax263307.WeightedAlgorithm.exists_solver
---
The blow-up class has the required power bag bound. Apply the computed
unweighted solver at half the requested accuracy, transport its answer
through the explicit labeling, and use the checked weighted projection.
-/
theorem exists_solver (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ (lp flow : List ℕ → List ℕ) (a K B : ℕ),
      Lax759944.RamPolytime.RamPolytime lp ∧ Lax759944.RamPolytime.RamPolytime flow ∧
      0 < a ∧ 0 < K ∧ 0 < B ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G ∈ C n →
      ∀ (w : Fin n → ℚ) (ε : ℚ), 0 < ε → ε < 1 → IsApproximation G w ε (solve lp flow a K B G w ε) := by
  obtain ⟨a, A, ha, hA, hbound⟩ := Lax263307.BlowUpBagBounds.blowup_power_bag_bound C hereditary separators
  obtain ⟨lp, flow, K, B, hpolyLP, hpolyFlow, hK, hB, hunweighted⟩ :=
    Lax263307.RecursiveAlgorithm.exists_solver (blowUpClass C) (hereditary_closure C) a A ha hA hbound
  refine ⟨lp, flow, a, K, B, hpolyLP, hpolyFlow, ha, hK, hB, ?_⟩
  intro n G _ hG w ε hε hεsmall
  dsimp only [solve]
  split_ifs with htrivial
  · apply Lax263307.PositiveWeights.nonpositive_case G w _ ε hε.le hεsmall.le
    intro v
    rcases htrivial with hn | hw
    · exact False.elim (by have := v.isLt; omega)
    · have hmax : positiveWeights w v ≤ maximumWeight (positiveWeights w) := by
        apply Finset.le_max'
        simp
      exact (le_max_left (w v) 0).trans (hmax.trans hw)
  · have hn : 0 < n := by omega
    have hmax : 0 < maximumWeight (positiveWeights w) := by exact lt_of_not_ge (fun h => htrivial (Or.inr h))
    let cp := copies (positiveWeights w) ε
    let H := numbered G cp
    have hclass : H ∈ blowUpClass C (∑ v, cp v) :=
      copy_graph_mem C G hG cp _ (labeling cp)
    have happrox := hunweighted _ H hclass (ε/2) (by positivity) (by linarith)
    apply Lax263307.PositiveWeights.signed_weight_transfer G w ε hε.le hεsmall.le
    apply Lax263307.WeightedProjection.approximation_transfer G (positiveWeights w) ε
      (fun v => le_max_right _ _) hn hε hεsmall hmax
    exact relabel_approximation G cp (ε/2) _ happrox

end Lax263307Proofs.WeightedAlgorithm
