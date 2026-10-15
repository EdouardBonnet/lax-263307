import Lax263307Proofs.NativeNearExecution
import Lax263307.RecursiveAlgorithm

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeOracleExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeCoreMachine NativeMachineSegment NativeOracleContext

def projection {n r : ℕ} (lp : List ℕ → List ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k D F : ℕ) (center : MomentLP.Index n r → ℚ) : RationalProjection.Outcome (MomentLP.dimension n r) :=
  RationalProjection.classify (MomentLP.program G k r) (NativeNodeTolerance.tolerance n D F)
    (RegisteredLP.certificate lp (DistanceProjection.distanceProgram (MomentLP.program G k r) (ProjectedOracle.raw center)))

def reply {n r : ℕ} (flow : List ℕ → List ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D k p b load : ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) :
    RationalProjection.Outcome (MomentLP.dimension n r) → RoundedOracleSearch.Reply (MomentLP.dimension n r) (Finset (Fin n))
  | .reject => .reject
  | .far a _ => .cut (RationalCutBuffer.integerNormal a)
  | .near x => match NativeNearExecution.run flow G D k p b load (MomentLP.decode x) child with
    | .reject => .reject
    | .found I => .found I
    | .cut A C u => .cut (RationalCutBuffer.integerNormal
        (RoundedOracleSearch.rationalNormal (NativeComponentNormal.normal (r:=r) A C u)))

def Output {N n : ℕ} : RoundedOracleSearch.Reply N (Finset (Fin n)) → Env → Prop
  | .reject,σ => NativeRoundTrace.Stopped (none : Option (Finset (Fin n))) σ
  | .found I,σ => NativeRoundTrace.Stopped (some I) σ
  | .cut a,σ => σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=13 ∧
      Prefix (NativeRoundedQuery.normal a) "round.normal" σ

structure ProjectionBounds {n : ℕ} (D k r F M w oracleTime : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (extent : String → ℕ) : Prop where
  positive : 0<n
  denominator : 0<D
  floorPower : 0<F
  program : (encodeProgram (MomentLP.program G k r)).length+2<2^w
  rational : 2*M^2+3<2^w
  shape : 4*MomentLP.dimension n r+5<2^w
  scale : 4*MomentLP.dimension n r≤M
  tolerance : NativeNodeTolerance.guard n D F<2^w
  reply : n+19<2^w
  input : (encodeProgram (MomentLP.program G k r)).length≤extent "lp.input"
  word : 3*MomentLP.dimension n r<extent "lp.word"
  center : 3*MomentLP.dimension n r≤extent "projection.center"
  word3 : 3≤extent "lp.word"
  tolerance3 : 3≤extent "projection.tolerance"
  distance : NativeDistanceData.wordLength (NativeMomentAssembly.rowCount n r) (MomentLP.dimension n r)<extent "lp.word"
  addresses : oracleTime<extent "vm.addresses"
  values : oracleTime<extent "vm.values"
  output : oracleTime<extent "vm.output"
  source : 3*MomentLP.dimension n r≤extent "cut.source"
  normal : 3*MomentLP.dimension n r≤extent "round.normal"

theorem projection_variable (cfg : Config) (s : String)
    (hp : s∉NativeProjectionPrepare.command.wvars)
    (hd : s∉NativeDistanceInput.command.wvars) (ho : s∉NativeOracleScalars.reserved)
    (ht : s∉NativeProjectionTolerance.command.wvars) (hr : s∉NativeProjectionResult.command.wvars)
    (hs : s≠"machine.phase") :
    s∉((phases cfg)[4]'(by change 4<16; decide)).wvars := by
  have hcall := NativeProjectionTrace.oracle_variable cfg.lp cfg.lpWidth s hd ho ht hr
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,go,
    Com.wvars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem projection_array (cfg : Config) (s : String)
    (hp : s∉NativeProjectionPrepare.command.warrs)
    (hd : s∉NativeDistanceInput.command.warrs)
    (ho : s∉["vm.addresses","vm.values","vm.output","vm.input"])
    (ht : s∉NativeProjectionTolerance.command.warrs) (hr : s∉NativeProjectionResult.command.warrs) :
    s∉((phases cfg)[4]'(by change 4<16; decide)).warrs := by
  have hcall := NativeOracleFrame.command_array cfg.lp cfg.lpWidth s ho
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,go,
    NativeProjectionOracle.command,NativeDistanceOracle.command,
    Com.warrs,List.mem_append,List.not_mem_nil,not_false_eq_true,not_or,and_true]

theorem projection_frame {n B D k r p b load F fuel S v limit t : ℕ} (cfg : Config)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent : String → ℕ} {front : List ℕ}
    {σ τ : Env} (rr : Run B ((phases cfg)[4]'(by change 4<16; decide)) σ τ t)
    (hc : Context B D k r p b load F fuel S v limit cfg G extent front σ) :
    Context B D k r p b load F fuel S v limit cfg G extent front τ := by
  apply NativeOracleContext.frame rr hc
  · intro s hs
    simp only [scalars,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro s hs
    simp only [arrays,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)

/-- One complete oracle execution from phase 4. Every native branch is
composed here, including smaller-fuel child runs in the near branch. The
result is ready for the actual rounded update, or for the node return. -/
theorem oracle_segment {n r : ℕ} (D k p b load F fuel S v limit w M farM nearM h T space
    oracleTime callCost flowTime childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (j : ℕ) (state : RoundedOracleSearch.State (MomentLP.dimension n r))
    (bounds : ProjectionBounds D k r F M w oracleTime G extent)
    (hcenter : ∀ i,NativeSignedArithmetic.Bounded M (state.2 i))
    (hquery : (encodeProgram (DistanceProjection.distanceProgram (MomentLP.program G k r)
      (ProjectedOracle.raw state.2))).length<extent "vm.input")
    (call : Spec (2^w) (NativeProjectionTrace.InvocationInput (MomentLP.program G k r)
      (ProjectedOracle.raw state.2) (NativeNodeTolerance.tolerance n D F) oracleTime)
      (NativeProjectionOracle.command cfg.lp cfg.lpWidth)
      (fun _ τ => NativeProjectionResult.Output (projection lp G k D F state.2) τ ∧
        τ.vars "projection.n"=MomentLP.dimension n r) callCost)
    (farBounds : ∀ a β,projection lp G k D F state.2=.far a β →
      (∀ i,NativeSignedArithmetic.Bounded farM (a i)) ∧
      farM*RationalCutBuffer.denominator a+farM+RationalCutBuffer.denominator a+
        3*MomentLP.dimension n r+23<2^w)
    (nearSetup : ∀ x,projection lp G k D F state.2=.near x →
      NativeNearExecution.Setup D k p b load fuel S v nearM h T w space flowTime childSteps childTime
        cfg G flow x extent front child)
    (σ : Env) (hc : Context (2^w) D k r p b load F fuel S v limit cfg G extent front σ)
    (hs : NativeRoundedTrace.StoredState j state σ)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=4) :
    ∃ τ transitions total,Segment (2^w) (phases cfg) transitions total σ τ ∧
      transitions≤(childSteps+5)*(n+1)+6 ∧
      total≤(16*(encodeProgram (MomentLP.program G k r)).length+(36*M.size+124)*MomentLP.dimension n r+135+callCost+2)+
        14+(193*MomentLP.dimension n r+48)+
        NativeNearExecution.timeBound cfg n r nearM S h childTime flowTime+6 ∧
      Context (2^w) D k r p b load F fuel S v limit cfg G extent front τ ∧
      NativeRoundedTrace.StoredState j state τ ∧
      Output (reply flow G D k p b load child (projection lp G k D F state.2)) τ ∧ RootData σ τ := by
  obtain ⟨ν,first,hrν,hpν,resultν,dimensionν⟩ := NativeProjectionTrace.projection_segment
    (2^w) M n D F cfg (MomentLP.program G k r) state.2 (projection lp G k D F state.2)
    oracleTime callCost call bounds.positive bounds.denominator bounds.floorPower bounds.program
    bounds.rational bounds.shape bounds.scale hcenter bounds.tolerance σ
    ⟨hs.2.2.1,hs.2.1⟩ ⟨hc.moments.1.1,hc.nodeD,hc.floorPower⟩ hc.program hc.programLength
    hc.bounded.2.1 (by rw [hc.lengths]; exact bounds.input) (by rw [hc.lengths]; exact bounds.word)
    (by rw [hc.lengths]; exact bounds.center) (by rw [hc.lengths]; exact bounds.word3)
    (by rw [hc.lengths]; exact bounds.tolerance3) (by rw [hc.lengths]; exact bounds.distance)
    (by rw [hc.lengths]; exact hquery) (by rw [hc.lengths]; exact bounds.addresses)
    (by rw [hc.lengths]; exact bounds.values) (by rw [hc.lengths]; exact bounds.output) hr hp
  have r1 := NativeMachineFrame.single_run first ⟨4,by change 4<16; decide⟩ hp
  have hcν := projection_frame cfg r1 hc
  have rootν := root_frame r1
    (projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hsν := NativeNearExecution.stored_frame r1 hs
    ⟨projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
    ⟨projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide),
      projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  cases he : projection lp G k D F state.2 with
  | reject =>
    have result0 : NativeProjectionResult.Output (.reject : RationalProjection.Outcome (MomentLP.dimension n r)) ν := by
      simpa only [he] using resultν
    obtain ⟨τ,last,hout⟩ := NativeProjectionTrace.reject_segment (2^w) cfg bounds.reply ν result0 hcν.moments.1.1 hrν hpν
    have r2 := NativeMachineFrame.single_run last ⟨5,by change 5<16; decide⟩ hpν
    change Run (2^w) projectionReply ν τ _ at r2
    refine ⟨τ,_,_,NativeMachineSegment.append first last,by nlinarith,by omega,
      NativeOracleContext.frame r2 hcν (by decide) (by decide),
      NativeNearExecution.stored_frame r2 hsν (by decide) (by decide),?_,
      rootν.trans (root_frame r2 (by decide) (by decide))⟩
    simpa only [he,reply,Output] using hout
  | far a β =>
    obtain ⟨ha,hfar⟩ := farBounds a β he
    have resultA : NativeProjectionResult.Output (.far a β) ν := by simpa only [he] using resultν
    obtain ⟨τ,last,runningτ,phaseτ,normalτ⟩ := NativeProjectionTrace.far_segment
      (2^w) farM cfg a β hfar ha ν resultA dimensionν hcν.bounded.2.1
      (by rw [hcν.lengths]; exact bounds.source) (by rw [hcν.lengths]; exact bounds.word)
      (by rw [hcν.lengths]; exact bounds.normal) hrν hpν
    have r2 := NativeMachineFrame.single_run last ⟨5,by change 5<16; decide⟩ hpν
    change Run (2^w) projectionReply ν τ _ at r2
    refine ⟨τ,_,_,NativeMachineSegment.append first last,by nlinarith,by omega,
      NativeOracleContext.frame r2 hcν (by decide) (by decide),
      NativeNearExecution.stored_frame r2 hsν (by decide) (by decide),?_,
      rootν.trans (root_frame r2 (by decide) (by decide))⟩
    simpa only [he,reply,Output] using And.intro runningτ (And.intro phaseτ normalτ)
  | near x =>
    have resultX : NativeProjectionResult.Output (.near x) ν := by simpa only [he] using resultν
    obtain ⟨μ,second,eqμ,hrμ,hpμ,pointμ⟩ := NativeProjectionTrace.near_segment (2^w) cfg x
      (by have hh := bounds.reply; omega) ν resultX hrν hpν
    have r2 := NativeMachineFrame.single_run second ⟨5,by change 5<16; decide⟩ hpν
    change Run (2^w) projectionReply ν μ _ at r2
    have hcμ := NativeOracleContext.frame r2 hcν (by decide) (by decide)
    have hsμ := NativeNearExecution.stored_frame r2 hsν (by decide) (by decide)
    let setup := nearSetup x he
    obtain ⟨τ,s,t,last,hsteps,htime,hcτ,hsτ,hout,rootτ⟩ := NativeNearExecution.near_segment
      D k p b load F fuel S v limit nearM h T w space flowTime childSteps childTime cfg G flow x extent front child
      setup.bounds setup.hx setup.hselected setup.htarget setup.hspace setup.flowCall setup.recursive
      j state μ hcμ hsμ pointμ.2.1 hrμ hpμ
    refine ⟨τ,_,_,NativeMachineSegment.append first (NativeMachineSegment.append second last),
      by omega,by omega,hcτ,hsτ,?_,rootν.trans ((root_frame r2 (by decide) (by decide)).trans rootτ)⟩
    simp only [he,reply]
    cases ho : NativeNearExecution.run flow G D k p b load (MomentLP.decode x) child <;>
      simpa only [ho,NativeNearExecution.Output,Output,NativeCollectionExecution.Cut] using hout

/-- The composed execution computes exactly the paper's chosen oracle,
with the actual recursively restricted child solver. -/
theorem actual_reply {n : ℕ} (lp flow : List ℕ → List ℕ) (a K b D k fuel : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (center : MomentLP.Index n (AlgorithmParameters.level a K b n D) → ℚ) :
    let r := AlgorithmParameters.level a K b n D
    let child := fun C t => RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G C) t
    reply flow G D k (AlgorithmParameters.sparsity a K b n D) b (AlgorithmParameters.load b n D) child
      (projection lp G k D ((AlgorithmParameters.floorDenominator a K b n D)^r) center) =
      ProjectedOracle.run lp flow a K b D G k
        (fun C t => (child C t).map (fun I => I.image (label C))) center := by
  dsimp only
  unfold projection
  rw [NativeNodeTolerance.actual_tolerance]
  have near_eq (x : MomentLP.Index n (AlgorithmParameters.level a K b n D) → ℚ) :
      NativeNearExecution.run flow G D k (AlgorithmParameters.sparsity a K b n D) b
        (AlgorithmParameters.load b n D) (MomentLP.decode x)
        (fun C t => RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G C) t) =
      NearOracle.run flow a K b D G k (MomentLP.decode x)
        (fun C t => (RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G C) t).map
          (fun I => I.image (label C))) := by rfl
  cases he : RationalProjection.classify (MomentLP.program G k (AlgorithmParameters.level a K b n D))
      (ProjectedOracle.tolerance a K b n D)
      (RegisteredLP.certificate lp (DistanceProjection.distanceProgram
        (MomentLP.program G k (AlgorithmParameters.level a K b n D)) (ProjectedOracle.raw center))) <;>
    simp only [reply,ProjectedOracle.run,he,near_eq,NativeComponentNormal.normal] <;> rfl

/-- Numerical requirements, actual selected solver specifications, and the
smaller-fuel induction premise consumed by the full oracle composition. -/
structure Setup {n r : ℕ} (D k p b load F fuel S v w M farM nearM h T space
    oracleTime callCost flowTime childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (state : RoundedOracleSearch.State (MomentLP.dimension n r)) : Prop where
  bounds : ProjectionBounds D k r F M w oracleTime G extent
  hcenter : ∀ i,NativeSignedArithmetic.Bounded M (state.2 i)
  hquery : (encodeProgram (DistanceProjection.distanceProgram (MomentLP.program G k r)
      (ProjectedOracle.raw state.2))).length<extent "vm.input"
  call : Spec (2^w) (NativeProjectionTrace.InvocationInput (MomentLP.program G k r)
      (ProjectedOracle.raw state.2) (NativeNodeTolerance.tolerance n D F) oracleTime)
      (NativeProjectionOracle.command cfg.lp cfg.lpWidth)
      (fun _ τ => NativeProjectionResult.Output (projection lp G k D F state.2) τ ∧
        τ.vars "projection.n"=MomentLP.dimension n r) callCost
  farBounds : ∀ a β,projection lp G k D F state.2=.far a β →
      (∀ i,NativeSignedArithmetic.Bounded farM (a i)) ∧
      farM*RationalCutBuffer.denominator a+farM+RationalCutBuffer.denominator a+
        3*MomentLP.dimension n r+23<2^w
  nearSetup : ∀ x,projection lp G k D F state.2=.near x →
      NativeNearExecution.Setup D k p b load fuel S v nearM h T w space flowTime childSteps childTime
        cfg G flow x extent front child

end Lax263307Proofs.NativeOracleExecution
