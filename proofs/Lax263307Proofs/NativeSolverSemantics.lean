import Lax263307Proofs.NativeRecursiveOracle
import Lax263307Proofs.WeightedAlgorithm

namespace Lax263307Proofs.NativeSolverSemantics

open Lax263307 GraphClasses EdgeSublinearSeparators PowerBagBounds BlowUpClasses
open WeightedAlgorithm WeightRounding PositiveWeights WeightedIndependentSet

/-- Choose the canonical byte-level LP backend and the correct flow backend
once for the blow-up class. The same fixed functions satisfy both native
reader interfaces and the weighted algorithm's functional correctness. -/
theorem exists_solvers_with_parts (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ (lp flow : List ℕ → List ℕ) (a A K b : ℕ),
      Lax759944.RamPolytime.RamPolytime lp ∧ NativeEncodedLP.Encoded lp ∧
      Lax759944.RamPolytime.RamPolytime flow ∧ 0<a ∧ 0<A ∧ 0<K ∧ 0<b ∧
      HasPowerBagBound (blowUpClass C) a A ∧ NearOracle.SeparatorCorrect (blowUpClass C) flow a K b ∧ NativeRecursiveOracle.OracleCorrect (blowUpClass C) lp flow a K b ∧
      ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],G ∈ C n →
        ∀ weights ε,0<ε → ε<1 → IsApproximation G weights ε (solve lp flow a K b G weights ε) := by
  obtain ⟨a,A,ha,hA,hbound⟩ := BlowUpBagBounds.blowup_power_bag_bound C hereditary separators
  obtain ⟨lp,flow,K,b,hpolyLP,hlp,hpolyFlow,hK,hb,hsep,ho⟩ := NativeRecursiveOracle.exists_solvers_with_parts
    (blowUpClass C) (hereditary_closure C) a A ha hA hbound
  have hunweighted : ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],G ∈ blowUpClass C n →
      ∀ ε : ℚ,0<ε → ε<1 → IsApproximation G (fun _ => 1) ε (RecursiveAlgorithm.independentSet lp flow a K b G ε) := by
    intro n G _ hG ε hε hε1
    exact Lax263307Proofs.RecursiveAlgorithm.independentSet_correct (blowUpClass C) (hereditary_closure C)
      lp flow a K b (fun m H _ hH hm D k h hD hlarge child hc =>
        NativeRecursiveOracle.search_correct ho H hH hm D k h hD hlarge child hc) G hG ε hε hε1
  refine ⟨lp,flow,a,A,K,b,hpolyLP,hlp,hpolyFlow,ha,hA,hK,hb,hbound,hsep,ho,?_⟩
  intro n G _ hG w ε hε hεsmall
  dsimp only [solve]
  split_ifs with htrivial
  · apply PositiveWeights.nonpositive_case G w _ ε hε.le hεsmall.le
    intro v
    rcases htrivial with hn | hw
    · exact False.elim (by have := v.isLt; omega)
    · have hmax : positiveWeights w v≤maximumWeight (positiveWeights w) := by apply Finset.le_max'; simp
      exact (le_max_left (w v) 0).trans (hmax.trans hw)
  · have hn : 0<n := by omega
    have hmax : 0<maximumWeight (positiveWeights w) := lt_of_not_ge (fun h => htrivial (Or.inr h))
    let cp := copies (positiveWeights w) ε
    let H := numbered G cp
    have hclass : H ∈ blowUpClass C (∑ v,cp v) := copy_graph_mem C G hG cp _ (labeling cp)
    have happrox := hunweighted _ H hclass (ε/2) (by positivity) (by linarith)
    apply PositiveWeights.signed_weight_transfer G w ε hε.le hεsmall.le
    apply WeightedProjection.approximation_transfer G (positiveWeights w) ε
      (fun v => le_max_right _ _) hn hε hεsmall hmax
    exact Lax263307Proofs.WeightedAlgorithm.relabel_approximation G cp (ε/2) _ happrox

theorem exists_solvers (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ (lp flow : List ℕ → List ℕ) (a A K b : ℕ),
      Lax759944.RamPolytime.RamPolytime lp ∧ NativeEncodedLP.Encoded lp ∧
      Lax759944.RamPolytime.RamPolytime flow ∧ 0<a ∧ 0<A ∧ 0<K ∧ 0<b ∧
      HasPowerBagBound (blowUpClass C) a A ∧ NativeRecursiveOracle.OracleCorrect (blowUpClass C) lp flow a K b ∧
      ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],G ∈ C n →
        ∀ weights ε,0<ε → ε<1 → IsApproximation G weights ε (solve lp flow a K b G weights ε) := by
  obtain ⟨lp,flow,a,A,K,b,hpolyLP,hlp,hpolyFlow,ha,hA,hK,hb,hbound,hsep,ho,hcorrect⟩ :=
    exists_solvers_with_parts C hereditary separators
  exact ⟨lp,flow,a,A,K,b,hpolyLP,hlp,hpolyFlow,ha,hA,hK,hb,hbound,ho,hcorrect⟩

end Lax263307Proofs.NativeSolverSemantics
