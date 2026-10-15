import Lax263307Proofs.NativeSolverSemantics
import Lax263307Proofs.NativeSelectedBudget
import Lax263307Proofs.NativeRootResource

namespace Lax263307Proofs.NativeQptasImplementation

open Lax263307 GraphClasses BlowUpClasses WeightedIndependentSet

/-- All algorithm, backend and root-budget constants are selected once
for the graph class, before any graph, weights, accuracy or host word width. -/
structure Fixed (C : GraphClass) where
  cfg : NativeCoreMachine.Config
  lp : List ℕ → List ℕ
  flow : List ℕ → List ℕ
  projection : NativeSelectedLP.Program lp
  separator : NativeSelectedNear.Program flow
  roundedConstant : ℕ
  roundedPositive : 0<roundedConstant
  projectionCode : projection.code=cfg.lp
  projectionCoeff : projection.coeff=cfg.lpWidth
  separatorCode : separator.code=cfg.flow
  separatorCoeff : separator.coeff=cfg.flowWidth
  encoded : NativeEncodedLP.Encoded lp
  separatorCorrect : NearOracle.SeparatorCorrect (blowUpClass C) flow cfg.a cfg.K cfg.b
  oracleCorrect : NativeRecursiveOracle.OracleCorrect (blowUpClass C) lp flow cfg.a cfg.K cfg.b
  classK : 0<cfg.K
  classB : 0<cfg.b
  rounded : NativeOracleRounds.Program cfg.rounded roundedConstant
  semantic : ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],G∈C n →
    ∀ weights ε,0<ε → ε<1 → IsApproximation G weights ε (WeightedAlgorithm.solve lp flow cfg.a cfg.K cfg.b G weights ε)
  envelopeCoefficient : ℕ
  envelopeExponent : ℕ
  budgetCoefficient : ℕ
  budgetExponent : ℕ
  envelopeCoefficientPositive : 0<envelopeCoefficient
  envelopeExponentPositive : 0<envelopeExponent
  budgetCoefficientPositive : 0<budgetCoefficient
  budgetExponentPositive : 0<budgetExponent
  uniform : ∀ n D m,0<D → 0<m → m ≤ n → ParameterResources.resource cfg.a cfg.K cfg.b m D ≤
    NativeRootResource.envelope envelopeCoefficient envelopeExponent n D
  budget : ∀ R,NativeSelectedBudget.demand cfg projection separator roundedConstant R ≤ budgetCoefficient*(R+1)^budgetExponent

theorem exists_fixed (C : GraphClass) (hereditary : IsHereditary C)
    (separators : EdgeSublinearSeparators.HasStronglyEdgeSublinearSeparators C) : Nonempty (Fixed C) := by
  obtain ⟨lp,flow,a,A,K,b,hpoly,encoded,hflow,ha,hA,hK,hb,hbags,hsep,ho,semantic⟩ :=
    NativeSolverSemantics.exists_solvers_with_parts C hereditary separators
  obtain ⟨p⟩ := NativeSelectedLP.exists_program lp hpoly encoded
  obtain ⟨q⟩ := NativeSelectedNear.exists_program flow hflow
  obtain ⟨rounded,c,hc,hrounded⟩ := NativeOracleRounds.exists_program
  let cfg : NativeCoreMachine.Config := ⟨a,K,b,p.code,q.code,rounded,p.coeff,q.coeff⟩
  obtain ⟨E,d,hE,hd,uniform⟩ := NativeRootResource.uniform a K b hK
  obtain ⟨Q,e,hQ,he,budget⟩ := NativeSelectedBudget.exists_budget cfg p q c
  exact ⟨⟨cfg,lp,flow,p,q,c,hc,rfl,rfl,rfl,rfl,encoded,hsep,ho,hK,hb,hrounded,semantic,
    E,d,Q,e,hE,hd,hQ,he,uniform,budget⟩⟩

end Lax263307Proofs.NativeQptasImplementation
