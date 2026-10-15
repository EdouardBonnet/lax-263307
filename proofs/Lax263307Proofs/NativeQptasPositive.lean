import Lax263307Proofs.NativeQptasImplementation
import Lax263307Proofs.NativeUnweightedExecution
import Lax263307Proofs.NativeQptasZero
import Lax263307Proofs.NativeInputBounds

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeQptasPositive

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses BlowUpClasses WeightedIndependentSet
open NativeQptasImplementation NativeRootWorkspace

def copies {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) : Fin n → ℕ :=
  WeightRounding.copies (PositiveWeights.positiveWeights weights) ε
def order {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) : ℕ := ∑ v,copies weights ε v
def denominator (N : ℕ) (ε : ℚ) : ℕ := RecursiveAlgorithm.accuracyDenominator N (ε/2)
def resource {C : GraphClass} (i : Fixed C) (N : ℕ) (ε : ℚ) : ℕ :=
  NativeRootResource.envelope i.envelopeCoefficient i.envelopeExponent N (denominator N ε)
def workspace {C : GraphClass} (i : Fixed C) (N : ℕ) (ε : ℚ) : ℕ :=
  i.budgetCoefficient*(resource i N ε+1)^i.budgetExponent

def budgetCost {C : GraphClass} (i : Fixed C) (N : ℕ) (ε : ℚ) : ℕ :=
  12*N.size+12*(2*N).size+12*i.envelopeExponent+
    12*(i.envelopeCoefficient*(denominator N ε*AlgorithmParameters.logarithm N)^i.envelopeExponent)+
    12*i.budgetExponent+78

def cost {C : GraphClass} (i : Fixed C) (n N : ℕ) (ε : ℚ) : ℕ :=
  NativeBlowUp.cost n N+(16*(N*N)+14)+18+(14*RecursionDepth.depth N+28)+budgetCost i N ε+
    NativeUnweightedExecution.cost i.cfg N (workspace i N ε)+(24*n+44*N+36)+20

theorem positive_parameters {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ) (hN : 0<order weights ε) :
    0<n ∧ 0<WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights) := by
  have hn : 0<n := by
    by_contra hn
    have hz : n=0 := by omega
    subst n
    simpa [order] using hN
  refine ⟨hn,?_⟩
  by_contra hmax
  have hmax : WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights) ≤ 0 := le_of_not_gt hmax
  have hz (v : Fin n) : PositiveWeights.positiveWeights weights v=0 := by
    have hle : PositiveWeights.positiveWeights weights v ≤ WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights) := by
      apply Finset.le_max'; simp
    exact le_antisymm (hle.trans hmax) (le_max_right _ _)
  have hc (v : Fin n) : copies weights ε v=0 := by
    simp [copies,WeightRounding.copies,WeightRounding.roundedCopies,hz v]
  have he : order weights ε=0 := by simp only [order,hc,Finset.sum_const_zero]
  omega

theorem functional_result {C : GraphClass} (i : Fixed C) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (weights : Fin n → ℚ) (ε : ℚ) (hN : 0<order weights ε) :
    WeightedAlgorithm.solve i.lp i.flow i.cfg.a i.cfg.K i.cfg.b G weights ε=
      IndependentBlowUp.project ((RecursiveAlgorithm.solve i.lp i.flow i.cfg.a i.cfg.K i.cfg.b
        (denominator (order weights ε) ε) (WeightedAlgorithm.numbered G (copies weights ε))).1.image
          (WeightedAlgorithm.labeling (copies weights ε))) := by
  have hp := positive_parameters weights ε hN
  rw [WeightedAlgorithm.solve,if_neg (by
    rintro (hz|hm)
    · exact hp.1.ne' hz
    · exact not_le_of_gt hp.2 hm)]
  exact NativeWeightedOutput.discard_projected weights ε _

structure Bounds {C : GraphClass} (i : Fixed C) (n N M w : ℕ) (ε : ℚ) : Prop where
  allocation : n*n+N*N+3*n+N+3 ≤ workspace i N ε
  frontend : 2*M^4+3<2^w
  input : n*n+3*n+3<2^w
  graph : n*n+N*N+n+N+3<2^w
  copy : N*N+N+5<2^w
  accuracy : 3*M+8*(RecursionDepth.depth N+1)*M+2*N+RecursionDepth.depth N+40<2^w
  budget : NativeRootBudget.guard i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent
    N (denominator N ε)<2^w
  host : hostHeight i.cfg (workspace i N ε) ≤ w
  output : n+N+5<2^w

theorem command_spec {C : GraphClass} (i : Fixed C) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G∈C n) (weights : Fin n → ℚ) (ε : ℚ) (hε : 0<ε)
    (M w : ℕ) (hM : 1 ≤ M) (hnM : n ≤ M)
    (hweights : ∀ v,NativeSignedArithmetic.Bounded M (weights v))
    (haccuracy : NativeSignedArithmetic.Bounded M ε) (hN : 0<order weights ε)
    (bounds : Bounds i n (order weights ε) M w ε) :
    let N := order weights ε
    let W := workspace i N ε
    let ext := extent i.cfg N W n
    Spec (2^w) (fun σ => σ.inp=encodeInput G weights ε ∧ NativeStateBounds.Bounded (2^w) σ ∧
        ∀ a,(σ.arrs a).length=ext a)
      (NativeQptasProgram.command i.cfg i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent)
      (fun σ τ => τ.out=σ.out++encodeOutput (WeightedAlgorithm.solve i.lp i.flow i.cfg.a i.cfg.K i.cfg.b G weights ε))
      (cost i n N ε) := by
  dsimp only
  let N := order weights ε
  let D := denominator N ε
  let R := resource i N ε
  let W := workspace i N ε
  let H := WeightedAlgorithm.numbered G (copies weights ε)
  let ext := extent i.cfg N W n
  change 0<N at hN
  change Bounds i n N M w ε at bounds
  have allocation : n*n+N*N+3*n+N+3 ≤ W := bounds.allocation
  have outputBound : n+N+5<2^w := bounds.output
  have hD : 4 ≤ D := (Lax263307Proofs.RecursiveAlgorithm.accuracy_budget N (ε/2) (by positivity)).1
  have uniform := i.uniform N D
  have hresource := uniform N (by omega) hN (Nat.le_refl N)
  change ParameterResources.resource i.cfg.a i.cfg.K i.cfg.b N D ≤ R at hresource
  have hnR : N ≤ R := by dsimp only [ParameterResources.resource] at hresource; omega
  have hclass : H∈blowUpClass C N := copy_graph_mem C G hG (copies weights ε) _ (WeightedAlgorithm.labeling _)
  have budget : NativeSelectedBudget.demand i.cfg i.projection i.separator i.roundedConstant R ≤ W := i.budget R
  have hguards := NativeUnweightedExecution.guards i.cfg N R W w hnR (by
    have h := budget; dsimp only [NativeSelectedBudget.demand] at h; omega) bounds.host
  have core := NativeUnweightedExecution.command_spec (hereditary_closure C) i.projection i.separator i.cfg
    i.projectionCode i.projectionCoeff i.separatorCode i.separatorCoeff i.encoded i.separatorCorrect
    i.oracleCorrect i.classK i.classB H hclass hN D i.roundedConstant n R W w hD hnR i.rounded
    (fun m hm hmn => uniform m (by omega) hm hmn) budget bounds.host
  have hMlt : M<2^w := by
    have hm := le_self_pow hM (by decide : 4≠0)
    nlinarith only [hm,bounds.frontend]
  intro σ hi
  have room (a : String) (ha : a∉["recursion.frames","image.output","weighted.output"]) :
      n*n+N*N+3*n+N+3 ≤ (σ.arrs a).length := by
    rw [hi.2.2 a,ordinary i.cfg N W n a ha]
    have h := allocation
    dsimp only [stride]
    omega
  obtain ⟨σ₁,r1,matrix₁,owners₁,order₁,data₁,out₁,input₁⟩ := NativeBlowUp.prepare_spec (2^w) M hM hnM G weights ε
    hε hweights haccuracy bounds.frontend bounds.input (by rw [pow_two]; change n*n+N*N+n+N+3<2^w; exact bounds.graph) σ
    ⟨hi.1,by have h := room "input.data" (by decide); omega,
      by have h := room "copy.counts" (by decide); omega,
      (show N ≤ (σ.arrs "blowup.owner").length from by have h := room "blowup.owner" (by decide); omega),
      (show N*N ≤ (σ.arrs "blowup.matrix").length from by have h := room "blowup.matrix" (by decide); omega)⟩
  change Run (2^w) NativeBlowUp.prepare σ σ₁ (NativeBlowUp.cost n N) at r1
  change σ₁.vars "blowup.length"=N at order₁
  change Prefix (NativeWeightReduction.adjacency H) "blowup.matrix" σ₁ at matrix₁
  change Prefix (NativeBlowUp.owners (copies weights ε)) "blowup.owner" σ₁ at owners₁
  let σ₂ := σ₁.setVar "graph.n" N
  have r2 : Run (2^w) NativeQptasProgram.order σ₁ σ₂ 2 := Run.assign (by
    rw [evalB_var_iff]
    exact ⟨order₁.symm,order₁ ▸ (by have h := outputBound; omega)⟩)
  obtain ⟨σ₃,r3,graph₃⟩ := NativeQptasProgram.copy_graph_spec (2^w) H bounds.copy σ₂
    ⟨(show σ₂.vars "graph.n"=N from by simp [σ₂]),by simpa only [Prefix,σ₂,arrs_setVar] using matrix₁,
      (show N*N ≤ (σ₂.arrs "search.graph").length from by rw [RamFrames.run_array_length (r1.seq r2)]; have h := room "search.graph" (by decide); omega)⟩
  change Run (2^w) NativeQptasProgram.copyGraph σ₂ σ₃ (16*(N*N)+14) at r3
  have input₃ : σ₃.vars "input.n"=n := ((r2.seq r3).frame_var _ (by decide)).trans input₁
  have data₃ : Prefix (NativeFrontend.tailInput G weights ε) "input.data" σ₃ := by
    simpa only [Prefix,(r2.seq r3).frame_arr "input.data" (by decide)] using data₁
  obtain ⟨σ₄,r4,accuracy₄⟩ := NativeOriginalAccuracy.command_spec (2^w) G weights ε bounds.input
    (haccuracy.1.trans_lt hMlt) (haccuracy.2.trans_lt hMlt) σ₃ ⟨input₃,data₃⟩
  obtain ⟨σ₅,r5,root₅⟩ := NativeRootAccuracy.command_spec (2^w) M N ε hε haccuracy bounds.accuracy σ₄
    ⟨(r4.frame_var _ (by decide)).trans graph₃.1,accuracy₄⟩
  obtain ⟨σ₆,r6,budget₆⟩ := NativeRootBudget.command_spec (2^w) i.envelopeCoefficient i.envelopeExponent
    i.budgetCoefficient i.budgetExponent N D hN (by omega) bounds.budget σ₅ ⟨root₅.1,root₅.2.2.1⟩
  have setup := r4.seq (r5.seq r6)
  have before := r2.seq (r3.seq setup)
  have graph₆ : Prefix (NativeWeightReduction.adjacency H) "search.graph" σ₆ := by
    simpa only [Prefix,setup.frame_arr "search.graph" (by
      change "search.graph"∉(Com.seq NativeOriginalAccuracy.command
        (.seq NativeRootAccuracy.command (NativeRootBudget.command 0 0 0 0))).warrs
      decide)] using graph₃.2
  have input₆ : NativeCoreExecution.Input (2^w) D (RecursionDepth.depth N) (stride W) W H ext σ₆ := by
    refine ⟨NativeStateBounds.run (r1.seq before) hi.2.1,⟨budget₆.1,graph₆⟩,budget₆.2.1,?_,budget₆.2.2.2.2,budget₆.2.2.2.1,?_⟩
    · exact (r6.frame_var _ (by change "recursion.fuel"∉(NativeRootBudget.command 0 0 0 0).wvars; decide)).trans root₅.2.2.2
    · intro a; rw [RamFrames.run_array_length (r1.seq before)]; exact hi.2.2 a
  obtain ⟨σ₇,r7,post₇⟩ := core σ₆ input₆
  change Run (2^w) (NativeCoreMachine.command i.cfg) σ₆ σ₇ (NativeUnweightedExecution.cost i.cfg N W) at r7
  have input₇ : σ₇.vars "input.n"=n := post₇.2.2.1.trans ((before.frame_var _ (by
    change "input.n"∉(Com.seq NativeQptasProgram.order (.seq NativeQptasProgram.copyGraph
      (.seq NativeOriginalAccuracy.command (.seq NativeRootAccuracy.command (NativeRootBudget.command 0 0 0 0))))).wvars
    decide)).trans input₁)
  have order₇ : σ₇.vars "blowup.length"=N := post₇.2.2.2.1.trans ((before.frame_var _ (by
    change "blowup.length"∉(Com.seq NativeQptasProgram.order (.seq NativeQptasProgram.copyGraph
      (.seq NativeOriginalAccuracy.command (.seq NativeRootAccuracy.command (NativeRootBudget.command 0 0 0 0))))).wvars
    decide)).trans order₁)
  have owners₇ : Prefix (NativeBlowUp.owners (copies weights ε)) "blowup.owner" σ₇ := by
    simpa only [Prefix,post₇.2.2.2.2.1,before.frame_arr "blowup.owner" (by
      change "blowup.owner"∉(Com.seq NativeQptasProgram.order (.seq NativeQptasProgram.copyGraph
        (.seq NativeOriginalAccuracy.command (.seq NativeRootAccuracy.command (NativeRootBudget.command 0 0 0 0))))).warrs
      decide)] using owners₁
  obtain ⟨τ,r8,output₈⟩ := NativeWeightedOutput.command_spec (2^w) (copies weights ε)
    (RecursiveAlgorithm.solve i.lp i.flow i.cfg.a i.cfg.K i.cfg.b D H).1 bounds.output hguards.2.2 σ₇
    ⟨input₇,order₇,post₇.2.1.1,owners₇,
      (show N ≤ (σ₇.arrs "image.labels").length from by rw [RamFrames.run_array_length ((r1.seq before).seq r7)]; have h := room "image.labels" (by decide); omega),
      by rw [RamFrames.run_array_length ((r1.seq before).seq r7),hi.2.2]; simp [ext,extent]⟩
  change Run (2^w) NativeWeightedOutput.command σ₇ τ (24*n+44*N+36) at r8
  have test : (Cond.eq (.var "graph.n") (.lit 0)).evalB (2^w) σ₂=some false := by
    have he := evalB_condEq (show (Expr.var "graph.n").evalB (2^w) σ₂=some N from by
      rw [evalB_var_iff]; exact ⟨by simp [σ₂],by simp only [σ₂,vars_setVar,ite_true]; omega⟩)
      (evalB_lit (show 0<2^w by omega))
    simpa [ne_of_gt hN] using he

  have run : Run (2^w) (NativeQptasProgram.command i.cfg i.envelopeCoefficient i.envelopeExponent
      i.budgetCoefficient i.budgetExponent) σ τ _ :=
    r1.seq <| r2.seq <| Run.ite_false test <| r3.seq <| r4.seq <| r5.seq <| r6.seq <| r7.seq r8
  refine ⟨τ,run.mono ?_,?_⟩
  · change _ ≤ cost i n N ε
    dsimp only [cost,budgetCost,D,W]
    simp only [Cond.size,Expr.size]
    omega
  · rw [functional_result i G weights ε hN]
    have out₆ : σ₆.out=σ.out := (before.out_eq (by
      change (Com.seq NativeQptasProgram.order (.seq NativeQptasProgram.copyGraph
        (.seq NativeOriginalAccuracy.command (.seq NativeRootAccuracy.command (NativeRootBudget.command 0 0 0 0))))).NoWrite
      decide)).trans out₁
    simpa only [post₇.2.2.2.2.2,out₆] using output₈

end Lax263307Proofs.NativeQptasPositive
