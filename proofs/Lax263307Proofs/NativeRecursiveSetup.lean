import Lax263307Proofs.NativeNodeProtocol
import Lax263307Proofs.NativeOracleRounds

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeRecursiveSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning ComputedSeparators RoundedOracleSearch
open NativeCoreMachine NativeMachineSegment NativeOracleContext NativeNodeProtocol

structure Near {n r : ℕ} (D k p b load fuel S v M h T w space flowTime childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (flow : List ℕ → List ℕ) (x : Fin (NativeCatalogMetadata.N n r) → ℚ)
    (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) (eligible : Eligible) : Prop where
  bounds : NativeNearExecution.Bounds n r D k p M h T fuel S w cfg extent front
  hx : ∀ i,NativeSignedArithmetic.Bounded M (x i)
  hselected : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A → A.card≤r
  htarget : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A →
      ∀ C,ComputedRounding.target (1/(D : ℚ)) (∑ v∈C,(NearOracle.costs (MomentLP.decode x) A v : ℚ))≤T
  hspace : ∀ a∈NativeSeparatorContext.workspace,space≤extent a
  flowCall : ∀ A,let costs := NearOracle.costs (MomentLP.decode x) A
      let cs := cuts (step flow G costs b load k) n Finset.univ
      Spec (2^w) (fun σ => NativeSeparatorContext.Context G costs b load k space σ ∧
          n+1≤(σ.arrs "separator.pieces").length)
        (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
        (fun _ τ => NativeSeparatorContext.Context G costs b load k space τ ∧
          τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs) ∧
          τ.vars "separator.value"=NativeMasks.mask (separator cs) ∧ τ.vars "separator.count"=cs.length ∧
          Prefix (NativeCutRecords.words cs) "separator.cuts" τ ∧ τ.vars "separator.position"=2*cs.length ∧
          Prefix (NativeCutPieces.words cs) "separator.pieces" τ) flowTime
  children : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A →
    let costs := NearOracle.costs (MomentLP.decode x) A
    let cs := cuts (step flow G costs b load k) n Finset.univ
    ∀ i∈NearOracle.order cs.length,
    (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈pieces cs i,(costs v : ℚ)) → eligible fuel (pieces cs i).card (restriction G (pieces cs i))
      (ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ)))
      (front.length+S*(frameArrays cfg).length+(frameScalars cfg).length)

structure Oracle {n r : ℕ} (D k p b load F fuel S v w M farM nearM h T space
    oracleTime callCost flowTime childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (state : RoundedOracleSearch.State (MomentLP.dimension n r)) (eligible : Eligible) : Prop where
  bounds : NativeOracleExecution.ProjectionBounds D k r F M w oracleTime G extent
  hcenter : ∀ i,NativeSignedArithmetic.Bounded M (state.2 i)
  hquery : (encodeProgram (DistanceProjection.distanceProgram (MomentLP.program G k r)
      (ProjectedOracle.raw state.2))).length<extent "vm.input"
  call : Spec (2^w) (NativeProjectionTrace.InvocationInput (MomentLP.program G k r)
      (ProjectedOracle.raw state.2) (NativeNodeTolerance.tolerance n D F) oracleTime)
      (NativeProjectionOracle.command cfg.lp cfg.lpWidth)
      (fun _ τ => NativeProjectionResult.Output (NativeOracleExecution.projection lp G k D F state.2) τ ∧
        τ.vars "projection.n"=MomentLP.dimension n r) callCost
  farBounds : ∀ a β,NativeOracleExecution.projection lp G k D F state.2=.far a β →
      (∀ i,NativeSignedArithmetic.Bounded farM (a i)) ∧
      farM*RationalCutBuffer.denominator a+farM+RationalCutBuffer.denominator a+
        3*MomentLP.dimension n r+23<2^w
  nearSetup : ∀ x,NativeOracleExecution.projection lp G k D F state.2=.near x →
      Near D k p b load fuel S v nearM h T w space flowTime childSteps childTime
        cfg G flow x extent front child eligible

structure Rounds {n r : ℕ} (D k p b load F fuel S v limit w M farM nearM costH T space
    oracleTime callCost flowTime childSteps childTime c roundH oracleCost roundCost : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (eligible : Eligible) : Prop where
  program : NativeOracleRounds.Program cfg.rounded c
  setup : ∀ j,j<limit → Oracle
      D k p b load F fuel S v w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime
      cfg G lp flow extent front child (trajectory (NativeOracleRounds.oracle (r:=r) lp flow G D k p b load F child) j) eligible
  rounded : ∀ j,j<limit → ∀ a,
      NativeOracleRounds.oracle (r:=r) lp flow G D k p b load F child j
        (trajectory (NativeOracleRounds.oracle (r:=r) lp flow G D k p b load F child) j).2=.cut a →
      NativeOracleRounds.Bounds (2^w) c roundH v n j limit cfg.rounded extent
        (trajectory (NativeOracleRounds.oracle (r:=r) lp flow G D k p b load F child) j) a
  hcost : (16*(Lax109476.RationalEncoding.encodeProgram (MomentLP.program G k r)).length+
      (36*M.size+124)*MomentLP.dimension n r+135+callCost+2)+14+(193*MomentLP.dimension n r+48)+
      NativeNearExecution.timeBound cfg n r nearM S costH childTime flowTime+6≤oracleCost
  hround : ∀ j,j<limit → NativeRoundedUpdate.timeBound cfg.rounded c (MomentLP.dimension n r) roundH j+16≤roundCost

theorem Near.to_setup {n r D k p b load fuel S v M h T w space flowTime childSteps childTime : ℕ}
    {cfg : Config} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {flow : List ℕ → List ℕ} {x : Fin (NativeCatalogMetadata.N n r) → ℚ}
    {extent : String → ℕ} {front : List ℕ} {eligible : Eligible}
    {child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))}
    (data : Near D k p b load fuel S v M h T w space flowTime childSteps childTime cfg G flow x extent front child eligible)
    (ih : Children (2^w) D fuel S v childSteps childTime cfg G extent front eligible child) :
    NativeNearExecution.Setup D k p b load fuel S v M h T w space flowTime childSteps childTime
      cfg G flow x extent front child := by
  refine ⟨data.bounds,data.hx,data.hselected,data.htarget,data.hspace,data.flowCall,?_⟩
  intro A choice
  dsimp only
  intro i hi heavy base σ hp hσ hd hm ht hr phase
  exact ih _ _ σ (data.children A choice i hi heavy) hp phase

theorem Oracle.to_setup {n r D k p b load F fuel S v w M farM nearM h T space
    oracleTime callCost flowTime childSteps childTime : ℕ}
    {cfg : Config} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {lp flow : List ℕ → List ℕ} {extent : String → ℕ} {front : List ℕ} {eligible : Eligible}
    {child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))}
    {state : State (MomentLP.dimension n r)}
    (data : Oracle D k p b load F fuel S v w M farM nearM h T space oracleTime callCost flowTime childSteps childTime
      cfg G lp flow extent front child state eligible)
    (ih : Children (2^w) D fuel S v childSteps childTime cfg G extent front eligible child) :
    NativeOracleExecution.Setup D k p b load F fuel S v w M farM nearM h T space oracleTime callCost flowTime
      childSteps childTime cfg G lp flow extent front child state :=
  ⟨data.bounds,data.hcenter,data.hquery,data.call,data.farBounds,fun x hx => (data.nearSetup x hx).to_setup ih⟩

theorem Rounds.to_setup {n r D k p b load F fuel S v limit w M farM nearM costH T space
    oracleTime callCost flowTime childSteps childTime c roundH oracleCost roundCost : ℕ}
    {cfg : Config} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {lp flow : List ℕ → List ℕ} {extent : String → ℕ} {front : List ℕ} {eligible : Eligible}
    {child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))}
    (data : Rounds (r:=r) D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime
      childSteps childTime c roundH oracleCost roundCost cfg G lp flow extent front child eligible)
    (ih : Children (2^w) D fuel S v childSteps childTime cfg G extent front eligible child) :
    NativeOracleRounds.Setup (r:=r) D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime
      childSteps childTime c roundH oracleCost roundCost cfg G lp flow extent front child :=
  ⟨data.program,fun j hj => (data.setup j hj).to_setup ih,data.rounded,data.hcost,data.hround⟩

end Lax263307Proofs.NativeRecursiveSetup
