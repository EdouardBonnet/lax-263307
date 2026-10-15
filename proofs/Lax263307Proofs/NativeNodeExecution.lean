import Lax263307Proofs.NativeRecursiveSetup
import Lax263307Proofs.NativeRecursionBudget

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNodeExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters ComputedSeparators
open NativeCoreMachine NativeMachineSegment NativeOracleContext NativeNodeProtocol

abbrev level (cfg : Config) (n D : ℕ) := AlgorithmParameters.level cfg.a cfg.K cfg.b n D
abbrev dimension (cfg : Config) (n D : ℕ) := MomentLP.dimension n (level cfg n D)
abbrev limit (cfg : Config) (n D : ℕ) := iterations cfg.a cfg.K cfg.b n D
abbrev child {n : ℕ} (cfg : Config) (lp flow : List ℕ → List ℕ) (D fuel : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :=
  fun C t => RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel (restriction G C) t

/-- All arithmetic and allocation obligations of the actual entry, small
and large initialization phases. This record contains no execution premise. -/
structure Bounds (w D k fuel n : ℕ) (cfg : Config) (extent : String → ℕ) : Prop where
  dispatch : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+n+k+cutoff cfg.a cfg.K cfg.b n D+fuel+29<2^w
  exhaustive : n*n+(n+1)*(k+1)+n+k+24<2^w
  masks : 2^n<2^w
  choose : ∀ i≤n,∀ j≤k,i.choose j<2^w
  classK : 0<cfg.K
  parameters : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+k+cfg.b+5<2^w
  moment : NativeMomentSetup.guardBound n k (level cfg n D)<2^w
  precision : NativeNodePrecision.guard n D (dimension cfg n D)
    (floorDenominator cfg.a cfg.K cfg.b n D) (level cfg n D)<2^w
  round : 3*(dimension cfg n D*dimension cfg n D)+3*dimension cfg n D+20<2^w
  smallTable : (n+1)*(k+1)≤extent "choose.table"
  largeTable : (n+1)*(level cfg n D+3)≤extent "choose.table"
  bits : n≤extent "subset.bits"
  catalog : dimension cfg n D≤extent "catalog.mask"
  cards : dimension cfg n D≤extent "catalog.card"
  independent : dimension cfg n D≤extent "catalog.independent"
  input : NativeMomentInput.length n (level cfg n D)≤extent "lp.input"
  cache : NativeMomentInput.length n (level cfg n D)≤extent "moment.program"
  roundInput : 3*(dimension cfg n D*dimension cfg n D)+3*dimension cfg n D≤extent "lp.input"
  shape : 3*(dimension cfg n D*dimension cfg n D)≤extent "round.shape"
  center : 3*dimension cfg n D≤extent "round.center"

theorem small_input {n w D k fuel S v : ℕ} {cfg : Config} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {extent : String → ℕ} {front : List ℕ} {σ : Env}
    (bounds : Bounds w D k fuel n cfg extent) (hi : Input (2^w) D fuel S v cfg G k extent front σ) :
    NativeSmallAttempt.Input G k σ :=
  ⟨hi.order,hi.target,hi.graph,by rw [hi.protocol.lengths]; exact bounds.smallTable,
    by rw [hi.protocol.lengths]; exact bounds.bits⟩

theorem large_input {n w D k fuel S v : ℕ} {cfg : Config} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {extent : String → ℕ} {front : List ℕ} {σ : Env}
    (bounds : Bounds w D k fuel n cfg extent) (hi : Input (2^w) D fuel S v cfg G k extent front σ) :
    NativeLargeNode.Input (2^w) cfg.a cfg.K cfg.b D k G σ := by
  refine ⟨hi.order,hi.protocol.accuracy,hi.target,hi.graph,hi.protocol.bounded.2.1,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hi.protocol.lengths]; exact bounds.largeTable
  · rw [hi.protocol.lengths]; exact bounds.bits
  · rw [hi.protocol.lengths]; exact bounds.catalog
  · rw [hi.protocol.lengths]; exact bounds.cards
  · rw [hi.protocol.lengths]; exact bounds.independent
  · rw [hi.protocol.lengths]; exact bounds.input
  · rw [hi.protocol.lengths]; exact bounds.cache
  · rw [hi.protocol.lengths]; exact bounds.roundInput
  · rw [hi.protocol.lengths]; exact bounds.shape
  · rw [hi.protocol.lengths]; exact bounds.center

/-- The numeric search data at a large node, separated from child
execution. The recursive cost appears only in its proved linear coefficient. -/
structure Search {n : ℕ} (D k fuel S v w childSteps childTime localSteps localTime branches : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ) (eligible : Eligible) where
  M : ℕ
  farM : ℕ
  nearM : ℕ
  costH : ℕ
  T : ℕ
  space : ℕ
  oracleTime : ℕ
  callCost : ℕ
  flowTime : ℕ
  c : ℕ
  roundH : ℕ
  oracleLocal : ℕ
  roundCost : ℕ
  data : NativeRecursiveSetup.Rounds (r:=level cfg n D) D k (sparsity cfg.a cfg.K cfg.b n D)
    cfg.b (load cfg.b n D) ((floorDenominator cfg.a cfg.K cfg.b n D)^(level cfg n D))
    fuel S v (limit cfg n D) w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime
    c roundH (oracleLocal+(n+1)*childTime) roundCost cfg G lp flow extent front (child cfg lp flow D fuel G) eligible
  steps : 2+(5*(n+1)+7)*limit cfg n D≤localSteps
  time : NativeNodeTrace.entryCost cfg.a n+NativeLargeNode.cost cfg.a n (level cfg n D)+2+
    (oracleLocal+roundCost)*limit cfg n D≤localTime
  branching : (n+1)*limit cfg n D≤branches

/-- A complete large attempt, including entry, initialization, bounded
oracle search and all recursive child executions supplied by the IH. -/
theorem large_segment {n : ℕ} (D k fuel S v w childSteps childTime localSteps localTime branches : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ) (eligible : Eligible)
    (bounds : Bounds w D k (fuel+1) n cfg extent)
    (data : Search D k fuel S v w childSteps childTime localSteps localTime branches cfg G lp flow extent front eligible)
    (children : Children (2^w) D fuel S v childSteps childTime cfg G extent front eligible (child cfg lp flow D fuel G))
    (hsmall : ¬(k≤cutoff cfg.a cfg.K cfg.b n D ∨ n≤1)) (hk : k≤n)
    (σ : Env) (hi : Input (2^w) D (fuel+1) S v cfg G k extent front σ)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=1) :
    ∃ τ s t,Segment (2^w) (phases cfg) s t σ τ ∧ s≤localSteps+branches*childSteps ∧
      t≤localTime+branches*childTime ∧
      NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D (fuel+1) G k) τ ∧
      Protocol (2^w) D S v cfg extent front τ ∧ RootData σ τ ∧ GraphData G τ := by
  obtain ⟨ν,first,largeν,fuelν,hrν,hpν⟩ := NativeNodeTrace.search_entry_segment (2^w) cfg G D k (fuel+1)
    hsmall hk (by omega) bounds.dispatch σ (large_input bounds hi) hi.depth hr hp
  have r1 := NativeMachineFrame.single_run first ⟨1,by change 1<16; decide⟩ hp
  change Run (2^w) (NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14) σ ν _ at r1
  have protocolν := dispatch_frame cfg r1 hi.protocol
  obtain ⟨μ,second,largeμ,fuelμ,hrμ,hpμ⟩ := NativeNodeTrace.large_segment (2^w) cfg D k (fuel+1) G
    (by omega) bounds.classK bounds.parameters bounds.moment bounds.masks bounds.precision bounds.round
    ν largeν fuelν hrν hpν
  have r2 := NativeMachineFrame.single_run second ⟨3,by change 3<16; decide⟩ hpν
  change Run (2^w) (.seq (NativeLargeNode.command cfg.a cfg.K cfg.b) (go 4)) ν μ _ at r2
  have protocolμ := large_frame cfg r2 protocolν
  obtain ⟨contextμ,storedμ⟩ := NativeOracleContext.of_large (2^w) D k fuel S v cfg G extent front μ largeμ
    protocolμ.bounded protocolμ.lengths protocolμ.stack protocolμ.cursor protocolμ.stride fuelμ protocolμ.roundWidth protocolμ.frameLength
  obtain ⟨τ,s,t,third,hs,ht,contextτ,answerτ,rootτ⟩ := NativeOracleRounds.search_segment
    D k (sparsity cfg.a cfg.K cfg.b n D) cfg.b (load cfg.b n D)
    ((floorDenominator cfg.a cfg.K cfg.b n D)^(level cfg n D)) fuel S v (limit cfg n D) w
    data.M data.farM data.nearM data.costH data.T data.space data.oracleTime data.callCost data.flowTime childSteps childTime
    data.c data.roundH (data.oracleLocal+(n+1)*childTime) data.roundCost (precision cfg.a cfg.K cfg.b n D)
    cfg G lp flow extent front (child cfg lp flow D fuel G) (data.data.to_setup children) rfl μ contextμ storedμ hrμ hpμ
  have heq : NativeOracleRounds.oracle (r:=level cfg n D) lp flow G D k (sparsity cfg.a cfg.K cfg.b n D)
      cfg.b (load cfg.b n D) ((floorDenominator cfg.a cfg.K cfg.b n D)^(level cfg n D)) (child cfg lp flow D fuel G) =
      fun (_ : ℕ) center => ProjectedOracle.run lp flow cfg.a cfg.K cfg.b D G k
        (fun C t => (child cfg lp flow D fuel G C t).map (fun I => I.image (label C))) center := by
    funext j center
    exact NativeOracleExecution.actual_reply lp flow cfg.a cfg.K cfg.b D k fuel G center
  have attemptEq : RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D (fuel+1) G k =
      ProjectedOracle.search lp flow cfg.a cfg.K cfg.b D G k
        (fun C t => (child cfg lp flow D fuel G C t).map (fun I => I.image (label C))) := by
    rw [RecursiveAlgorithm.attempt,if_neg hsmall,if_neg (Nat.not_lt.mpr hk)]
  refine ⟨τ,_,_,NativeMachineSegment.append first (NativeMachineSegment.append second third),?_,?_,?_,
    NativeOracleContext.protocol contextτ,(dispatch_root cfg r1).trans ((large_root cfg r2).trans rootτ),
    contextτ.moments.1.1,contextτ.moments.1.2.2.2.1⟩
  · calc
      1+(1+s)≤2+((childSteps+5)*(n+1)+7)*limit cfg n D := by omega
      _=(2+(5*(n+1)+7)*limit cfg n D)+((n+1)*limit cfg n D)*childSteps := by ring
      _≤localSteps+branches*childSteps := Nat.add_le_add data.steps (Nat.mul_le_mul_right _ data.branching)
  · calc
      NativeNodeTrace.entryCost cfg.a n+(NativeLargeNode.cost cfg.a n (level cfg n D)+2+t)≤
          NativeNodeTrace.entryCost cfg.a n+NativeLargeNode.cost cfg.a n (level cfg n D)+2+
            ((data.oracleLocal+(n+1)*childTime)+data.roundCost)*limit cfg n D := by omega
      _=(NativeNodeTrace.entryCost cfg.a n+NativeLargeNode.cost cfg.a n (level cfg n D)+2+
          (data.oracleLocal+data.roundCost)*limit cfg n D)+((n+1)*limit cfg n D)*childTime := by ring
      _≤localTime+branches*childTime := Nat.add_le_add data.time (Nat.mul_le_mul_right _ data.branching)
  · rw [attemptEq]
    simpa only [heq,ProjectedOracle.search] using answerτ

theorem small_segment {n : ℕ} (D k fuel S v w : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lp flow : List ℕ → List ℕ)
    (extent : String → ℕ) (front : List ℕ) (bounds : Bounds w D k fuel n cfg extent)
    (hsmall : k≤cutoff cfg.a cfg.K cfg.b n D ∨ n≤1) (σ : Env)
    (hi : Input (2^w) D fuel S v cfg G k extent front σ)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=1) :
    ∃ τ,Segment (2^w) (phases cfg) 2 (NativeNodeTrace.entryCost cfg.a n+NativeExhaustive.cost n k+15*n+20) σ τ ∧
      NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) τ ∧
      Protocol (2^w) D S v cfg extent front τ ∧ RootData σ τ ∧ GraphData G τ := by
  obtain ⟨τ,trace,answer,order,graph,ν,r1,r2⟩ := NativeNodeTrace.exhaustive_segment (2^w) cfg lp flow G D k fuel
    hsmall bounds.dispatch bounds.exhaustive bounds.masks bounds.choose σ
    ⟨hi.order,hi.protocol.accuracy,hi.target,hi.depth⟩ (small_input bounds hi) hr hp
  exact ⟨τ,trace,answer,NativeNodeProtocol.frame r2 (dispatch_frame cfg r1 hi.protocol) (by decide) (by decide),
    (dispatch_root cfg r1).trans (root_frame r2 (by decide) (by decide)),order,graph⟩

theorem reject_segment {n : ℕ} (D k fuel S v w : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lp flow : List ℕ → List ℕ)
    (extent : String → ℕ) (front : List ℕ) (bounds : Bounds w D k fuel n cfg extent)
    (hsmall : ¬(k≤cutoff cfg.a cfg.K cfg.b n D ∨ n≤1)) (hreject : n<k ∨ fuel=0) (σ : Env)
    (hi : Input (2^w) D fuel S v cfg G k extent front σ)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=1) :
    ∃ τ,Segment (2^w) (phases cfg) 1 (NativeNodeTrace.entryCost cfg.a n) σ τ ∧
      NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) τ ∧
      Protocol (2^w) D S v cfg extent front τ ∧ RootData σ τ ∧ GraphData G τ := by
  obtain ⟨τ,trace,answer,hinput⟩ := NativeNodeTrace.reject_segment (2^w) cfg lp flow G D k fuel
    hsmall hreject bounds.dispatch σ ⟨hi.order,hi.protocol.accuracy,hi.target,hi.depth⟩ hr hp
  have rr := NativeMachineFrame.single_run trace ⟨1,by change 1<16; decide⟩ hp
  refine ⟨τ,trace,answer,dispatch_frame cfg rr hi.protocol,dispatch_root cfg rr,hinput.1,?_⟩
  simpa only [Prefix,rr.frame_arr "search.graph" (by
    change "search.graph"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs
    decide)] using hi.graph

/-- Uniform numerical and solver data for a family of recursive nodes.
Every child-domain condition is a mathematical condition on an actual
computed part; no recursive execution assumption occurs in this record. -/
structure Resources (D S v w localSteps localTime branches : ℕ) (cfg : Config)
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (eligible : Eligible) where
  frameExtents : ∀ a∈frameArrays cfg,extent a=S
  entry : ∀ fuel n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] k cursor,
    eligible fuel n G k cursor → Bounds w D k fuel n cfg extent
  entryCost : ∀ fuel n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] k cursor,
    eligible fuel n G k cursor → 1≤localSteps ∧ NativeNodeTrace.entryCost cfg.a n≤localTime
  small : ∀ fuel n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] k cursor,
    eligible fuel n G k cursor → (k≤cutoff cfg.a cfg.K cfg.b n D ∨ n≤1) →
    2≤localSteps ∧ NativeNodeTrace.entryCost cfg.a n+NativeExhaustive.cost n k+15*n+20≤localTime
  large : ∀ fuel n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] k (front : List ℕ),
    eligible (fuel+1) n G k front.length → ¬(k≤cutoff cfg.a cfg.K cfg.b n D ∨ n≤1) → k≤n →
    Search D k fuel S v w (NativeRecursionBudget.work localSteps branches fuel)
      (NativeRecursionBudget.work localTime branches fuel) localSteps localTime branches cfg G lp flow extent front eligible

theorem work_base (localCost branches fuel : ℕ) : localCost≤NativeRecursionBudget.work localCost branches fuel := by
  cases fuel <;> simp only [NativeRecursionBudget.work] <;> omega

/-- Fuel induction closes every actual child callback in the complete
native node execution. The resource contract above contains only numeric,
allocation, solver, and child-domain data. -/
theorem executes (D S v w localSteps localTime branches : ℕ) (cfg : Config)
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (eligible : Eligible)
    (resources : Resources D S v w localSteps localTime branches cfg lp flow extent eligible) :
    ∀ fuel,Executes (2^w) D fuel S v (NativeRecursionBudget.work localSteps branches fuel)
      (NativeRecursionBudget.work localTime branches fuel) cfg lp flow extent eligible := by
  intro fuel
  induction fuel with
  | zero =>
    intro n G _ k front σ hel hi hr hp
    have bounds := resources.entry 0 n G k front.length hel
    by_cases hsmall : k≤cutoff cfg.a cfg.K cfg.b n D ∨ n≤1
    · obtain ⟨τ,trace,answer,protocolτ,rootτ,graphτ⟩ := small_segment D k 0 S v w cfg G lp flow extent front bounds hsmall σ hi hr hp
      have caps := resources.small 0 n G k front.length hel hsmall
      exact ⟨τ,2,_,trace,caps.1,caps.2,answer,protocolτ,rootτ,graphτ⟩
    · obtain ⟨τ,trace,answer,protocolτ,rootτ,graphτ⟩ := reject_segment D k 0 S v w cfg G lp flow extent front bounds hsmall (by simp) σ hi hr hp
      have caps := resources.entryCost 0 n G k front.length hel
      exact ⟨τ,1,_,trace,caps.1,caps.2,answer,protocolτ,rootτ,graphτ⟩
  | succ fuel ih =>
    intro n G _ k front σ hel hi hr hp
    have bounds := resources.entry (fuel+1) n G k front.length hel
    by_cases hsmall : k≤cutoff cfg.a cfg.K cfg.b n D ∨ n≤1
    · obtain ⟨τ,trace,answer,protocolτ,rootτ,graphτ⟩ := small_segment D k (fuel+1) S v w cfg G lp flow extent front bounds hsmall σ hi hr hp
      have caps := resources.small (fuel+1) n G k front.length hel hsmall
      exact ⟨τ,2,_,trace,caps.1.trans (work_base _ _ _),caps.2.trans (work_base _ _ _),answer,protocolτ,rootτ,graphτ⟩
    · by_cases hk : n<k
      · obtain ⟨τ,trace,answer,protocolτ,rootτ,graphτ⟩ := reject_segment D k (fuel+1) S v w cfg G lp flow extent front bounds hsmall (Or.inl hk) σ hi hr hp
        have caps := resources.entryCost (fuel+1) n G k front.length hel
        exact ⟨τ,1,_,trace,caps.1.trans (work_base _ _ _),caps.2.trans (work_base _ _ _),answer,protocolτ,rootτ,graphτ⟩
      · have children := NativeNodeProtocol.children (2^w) D fuel S v
          (NativeRecursionBudget.work localSteps branches fuel) (NativeRecursionBudget.work localTime branches fuel)
          cfg lp flow G extent front eligible resources.frameExtents ih
        exact large_segment D k fuel S v w _ _ localSteps localTime branches cfg G lp flow extent front eligible bounds
          (resources.large fuel n G k front hel hsmall (by omega)) children hsmall (by omega) σ hi hr hp

end Lax263307Proofs.NativeNodeExecution
