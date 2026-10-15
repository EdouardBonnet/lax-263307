import Lax263307Proofs.NativeOracleExecution

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeOracleRounds

open Matrix
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment NativeOracleContext

/-- The actual program specification already proved by NativeRoundedControl. -/
def Program (p : Lax808846.Ram.Program) (c : ℕ) : Prop :=
    ∀ (n m k h limit projection ret : ℕ),2≤n → 1≤h →
    ∀ (state : State n) (a : Fin n → ℤ),
    (∀ i j,Lax263307.NativeRoundedStep.height (state.1 i j) h) →
    (∀ i,Lax263307.NativeRoundedStep.height (rationalNormal a i) h) →
    (∀ i,Lax263307.NativeRoundedStep.height (state.2 i) h) →
    0<rationalNormal a ⬝ᵥ (state.1 *ᵥ rationalNormal a) →
    ∀ (B v : ℕ),c*(n+h+k+1)^12≤v →
    let T := c*(n+h+k+1)^12
    let xs := Lax263307.NativeRoundedStep.encodeInput k state a
    2*(2^v)^2+3<B → T+1<B → RamVirtualConstants.allowance p<B → xs.length+3<B →
    m+k+limit+projection+ret+10<B → (∀ z∈xs,z<B) →
    Spec B (fun σ => NativeRoundedQuery.Data k state a σ ∧ σ.vars "algorithm.roundWidth"=v ∧
      σ.vars "graph.n"=m ∧ σ.vars "round.limit"=limit ∧
      xs.length≤(σ.arrs "vm.input").length ∧ T<(σ.arrs "vm.addresses").length ∧
      T<(σ.arrs "vm.values").length ∧ T<(σ.arrs "vm.output").length ∧
      3*(n*n)≤(σ.arrs "round.shape").length ∧ 3*n≤(σ.arrs "round.center").length)
      (NativeRoundedControl.command p projection ret) (fun _ τ => Prefix (NativeRoundedQuery.shape (update k state a)) "round.shape" τ ∧
        Prefix (NativeRoundedQuery.center (update k state a)) "round.center" τ ∧
        τ.vars "vec.n"=n ∧ NativeRoundedControl.Output m k limit projection ret τ)
      (NativeRoundedUpdate.timeBound p c n h k+16)

theorem exists_program : ∃ p c,0<c ∧ Program p c :=
  NativeRoundedControl.exists_program

structure Bounds {N : ℕ} (B c h v m j limit : ℕ) (p : Lax808846.Ram.Program)
    (extent : String → ℕ) (state : State N) (a : Fin N → ℤ) : Prop where
  dimension : 2≤N
  height : 1≤h
  shapeHeight : ∀ i k,NativeRoundedStep.height (state.1 i k) h
  normalHeight : ∀ i,NativeRoundedStep.height (rationalNormal a i) h
  centerHeight : ∀ i,NativeRoundedStep.height (state.2 i) h
  positive : 0<rationalNormal a ⬝ᵥ (state.1 *ᵥ rationalNormal a)
  width : c*(N+h+j+1)^12≤v
  host : 2*(2^v)^2+3<B
  time : c*(N+h+j+1)^12+1<B
  allowance : RamVirtualConstants.allowance p<B
  query : (NativeRoundedStep.encodeInput j state a).length+3<B
  scalars : m+j+limit+4+14+10<B
  words : ∀ z∈NativeRoundedStep.encodeInput j state a,z<B
  wordRoom : (NativeRoundedStep.encodeInput j state a).length≤extent "lp.word"
  inputRoom : (NativeRoundedStep.encodeInput j state a).length≤extent "vm.input"
  addresses : c*(N+h+j+1)^12<extent "vm.addresses"
  values : c*(N+h+j+1)^12<extent "vm.values"
  output : c*(N+h+j+1)^12<extent "vm.output"
  shapeRoom : 3*(N*N)≤extent "round.shape"
  centerRoom : 3*N≤extent "round.center"

theorem update_variable (cfg : Config) (s : String)
    (hv : s≠"vm.width") (hq : s∉NativeRoundedQuery.command.wvars)
    (hp : s∉NativeRawOracle.prepare.wvars) (ho : s∉NativeOracleScalars.reserved)
    (hs : s∉NativeRoundedState.command.wvars) (hf : s∉(NativeRoundedControl.finish 4 14).wvars) :
    s∉(NativeRoundedControl.command cfg.rounded 4 14).wvars := by
  have hu := NativeRoundedControl.update_variable cfg.rounded s hq hp ho hs
  simp_all only [NativeRoundedControl.command,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem update_array (cfg : Config) (s : String)
    (hq : s∉NativeRoundedQuery.command.warrs) (hp : s∉NativeRawOracle.prepare.warrs)
    (ho : s∉["vm.addresses","vm.values","vm.output","vm.input"])
    (hs : s∉NativeRoundedState.command.warrs) :
    s∉(NativeRoundedControl.command cfg.rounded 4 14).warrs := by
  have hu := NativeRawFrame.array cfg.rounded s hp ho
  simp_all only [NativeRoundedControl.command,NativeRoundedUpdate.command,
    NativeRoundedControl.finish,NativeAttemptReply.noneCommand,
    Com.warrs,List.mem_append,List.not_mem_nil,not_false_eq_true,not_or,and_true,true_and]

theorem update_frame {n B D k r p b load F fuel S v limit t : ℕ} (cfg : Config)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent : String → ℕ} {front : List ℕ}
    {σ τ : Env} (rr : Run B (NativeRoundedControl.command cfg.rounded 4 14) σ τ t)
    (hc : Context B D k r p b load F fuel S v limit cfg G extent front σ) :
    Context B D k r p b load F fuel S v limit cfg G extent front τ := by
  apply NativeOracleContext.frame rr hc
  · intro s hs
    simp only [NativeOracleContext.scalars,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact update_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · intro s hs
    simp only [NativeOracleContext.arrays,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact update_array cfg _ (by decide) (by decide) (by decide) (by decide)

/-- Execute the selected rounded program on the normal actually returned
by the composed oracle, and retain the entire fixed parent context. -/
theorem update_segment {n r : ℕ} (B D k p b load F fuel S v limit c h j : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (extent : String → ℕ) (front : List ℕ)
    (program : Program cfg.rounded c) (state : State (MomentLP.dimension n r))
    (a : Fin (MomentLP.dimension n r) → ℤ)
    (bounds : Bounds B c h v n j limit cfg.rounded extent state a)
    (σ : Env) (hc : Context B D k r p b load F fuel S v limit cfg G extent front σ)
    (hs : NativeRoundedTrace.StoredState j state σ)
    (hnormal : Prefix (NativeRoundedQuery.normal a) "round.normal" σ)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=13) :
    ∃ τ,Segment B (phases cfg) 1 (NativeRoundedUpdate.timeBound cfg.rounded c (MomentLP.dimension n r) h j+16) σ τ ∧
      Context B D k r p b load F fuel S v limit cfg G extent front τ ∧
      NativeRoundTrace.Outcome NativeRoundedTrace.StoredState limit j state
        (.cut a : Reply (MomentLP.dimension n r) (Finset (Fin n))) τ ∧ RootData σ τ := by
  have call := program (MomentLP.dimension n r) n j h limit 4 14 bounds.dimension bounds.height
    state a bounds.shapeHeight bounds.normalHeight bounds.centerHeight bounds.positive B v bounds.width
    bounds.host bounds.time bounds.allowance bounds.query bounds.scalars bounds.words
  obtain ⟨τ,rr,po⟩ := call σ ⟨⟨hs.2.2.1,hs.2.2.2,hs.1,hnormal,hs.2.1,
      by rw [hc.lengths]; exact bounds.wordRoom⟩,hc.roundWidth,hc.moments.1.1,hc.roundLimit,
    by rw [hc.lengths]; exact bounds.inputRoom,by rw [hc.lengths]; exact bounds.addresses,
    by rw [hc.lengths]; exact bounds.values,by rw [hc.lengths]; exact bounds.output,
    by rw [hc.lengths]; exact bounds.shapeRoom,by rw [hc.lengths]; exact bounds.centerRoom⟩
  have rrPhase : Run B ((phases cfg)[13]'(by change 13<16; decide)) σ τ _ := rr
  have runningτ := (rr.frame_var _ (update_variable cfg _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide))).trans hr
  refine ⟨τ,NativeMachineSegment.phase hr ⟨13,by change 13<16; decide⟩ hp rrPhase,
    update_frame cfg rr hc,?_,root_frame rr
      (update_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (update_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))⟩
  refine ⟨⟨po.1,po.2.1,po.2.2.1,po.2.2.2.2.1⟩,?_⟩
  by_cases hj : j+1<limit
  · simp only [hj,if_true]
    exact ⟨runningτ,by simpa only [NativeRoundedControl.Output,hj,if_true] using po.2.2.2.2.2⟩
  · simp only [hj,if_false]
    have hout : NativeTargetDriver.Reply (none : Option (Finset (Fin n))) τ ∧ τ.vars "machine.phase"=14 := by
      simpa only [NativeRoundedControl.Output,hj,if_false] using po.2.2.2.2.2
    exact ⟨runningτ,hout.2,hout.1⟩

def Invariant {N n : ℕ} (Base : Env → Prop) (oracle : ℕ → (Fin N → ℚ) → Reply N (Finset (Fin n)))
    (j : ℕ) (state : State N) (σ : Env) : Prop :=
  Base σ ∧ NativeRoundedTrace.StoredState j state σ ∧ state=trajectory oracle j

def oracle {n r : ℕ} (lp flow : List ℕ → List ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k p b load F : ℕ) (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) :
    ℕ → (MomentLP.Index n r → ℚ) → Reply (MomentLP.dimension n r) (Finset (Fin n)) :=
  fun _ center => NativeOracleExecution.reply flow G D k p b load child
    (NativeOracleExecution.projection lp G k D F center)

def WithRoot (root : Env) (Base : Env → Prop) (σ : Env) : Prop := Base σ ∧ RootData root σ

/-- Instantiate the bounded-round Steps contract from the complete native
oracle and the actual rounded program. Only numerical obligations and
smaller-fuel child execution remain in the supplied setups. -/
theorem steps {n r : ℕ} (D k p b load F fuel S v limit w M farM nearM costH T space
    oracleTime callCost flowTime childSteps childTime c roundH oracleCost roundCost : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (root : Env) (program : Program cfg.rounded c)
    (setup : ∀ j,j<limit → NativeOracleExecution.Setup
      D k p b load F fuel S v w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime
      cfg G lp flow extent front child (trajectory (oracle (r:=r) lp flow G D k p b load F child) j))
    (rounded : ∀ j,j<limit → ∀ a,
      oracle (r:=r) lp flow G D k p b load F child j
        (trajectory (oracle (r:=r) lp flow G D k p b load F child) j).2=.cut a →
      Bounds (2^w) c roundH v n j limit cfg.rounded extent
        (trajectory (oracle (r:=r) lp flow G D k p b load F child) j) a)
    (hcost : (16*(Lax109476.RationalEncoding.encodeProgram (MomentLP.program G k r)).length+
      (36*M.size+124)*MomentLP.dimension n r+135+callCost+2)+14+(193*MomentLP.dimension n r+48)+
      NativeNearExecution.timeBound cfg n r nearM S costH childTime flowTime+6≤oracleCost)
    (hround : ∀ j,j<limit → NativeRoundedUpdate.timeBound cfg.rounded c (MomentLP.dimension n r) roundH j+16≤roundCost) :
    NativeRoundTrace.Steps (2^w) cfg
      (WithRoot root (Context (2^w) D k r p b load F fuel S v limit cfg G extent front))
      (Invariant (WithRoot root (Context (2^w) D k r p b load F fuel S v limit cfg G extent front))
        (oracle (r:=r) lp flow G D k p b load F child))
      (oracle (r:=r) lp flow G D k p b load F child) limit
      ((childSteps+5)*(n+1)+7) (oracleCost+roundCost) := by
  intro j hj state σ hQ hr hp
  rcases hQ with ⟨⟨hc,hroot⟩,hs,rfl⟩
  let data := setup j hj
  obtain ⟨ν,s,t,first,hsteps,htime,hcν,hsν,replyν,rootν⟩ := NativeOracleExecution.oracle_segment
    D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime
    cfg G lp flow extent front child j (trajectory (oracle (r:=r) lp flow G D k p b load F child) j)
    data.bounds data.hcenter data.hquery data.call data.farBounds data.nearSetup σ hc hs hr hp
  have ht : t≤oracleCost := htime.trans hcost
  change NativeOracleExecution.Output (oracle (r:=r) lp flow G D k p b load F child j
    (trajectory (oracle (r:=r) lp flow G D k p b load F child) j).2) ν at replyν
  cases he : oracle (r:=r) lp flow G D k p b load F child j
      (trajectory (oracle (r:=r) lp flow G D k p b load F child) j).2 with
  | reject =>
    refine ⟨ν,s,t,first,by omega,by omega,⟨hcν,hroot.trans rootν⟩,?_⟩
    simpa only [he,NativeOracleExecution.Output,NativeRoundTrace.Outcome] using replyν
  | found I =>
    refine ⟨ν,s,t,first,by omega,by omega,⟨hcν,hroot.trans rootν⟩,?_⟩
    simpa only [he,NativeOracleExecution.Output,NativeRoundTrace.Outcome] using replyν
  | cut a =>
    have raw : ν.vars "machine.running"=1 ∧ ν.vars "machine.phase"=13 ∧
        Prefix (NativeRoundedQuery.normal a) "round.normal" ν := by
      simpa only [he,NativeOracleExecution.Output] using replyν
    obtain ⟨τ,last,hcτ,out,rootτ⟩ := update_segment (2^w) D k p b load F fuel S v limit c roundH j cfg G
      extent front program (trajectory (oracle (r:=r) lp flow G D k p b load F child) j) a
      (rounded j hj a he) ν hcν hsν raw.2.2 raw.1 raw.2.1
    have htRound := hround j hj
    refine ⟨τ,s+1,_,NativeMachineSegment.append first last,by omega,by omega,⟨hcτ,hroot.trans (rootν.trans rootτ)⟩,?_⟩
    have hout : NativeRoundedTrace.StoredState (j+1)
        (update j (trajectory (oracle (r:=r) lp flow G D k p b load F child) j) a) τ ∧
        if j+1<limit then τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=4
        else NativeRoundTrace.Stopped (none : Option (Finset (Fin n))) τ := out
    have next : update j (trajectory (oracle (r:=r) lp flow G D k p b load F child) j) a =
        trajectory (oracle (r:=r) lp flow G D k p b load F child) (j+1) := by
      simp only [trajectory,he,selectedNormal]
    simp only [he,NativeRoundTrace.Outcome]
    exact ⟨⟨⟨hcτ,hroot.trans (rootν.trans rootτ)⟩,hout.1,next⟩,hout.2⟩

/-- Requirements for the complete search, with no assumed Steps contract. -/
structure Setup {n r : ℕ} (D k p b load F fuel S v limit w M farM nearM costH T space
    oracleTime callCost flowTime childSteps childTime c roundH oracleCost roundCost : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
 : Prop where
  program : Program cfg.rounded c
  setup : ∀ j,j<limit → NativeOracleExecution.Setup
      D k p b load F fuel S v w M farM nearM costH T space oracleTime callCost flowTime childSteps childTime
      cfg G lp flow extent front child (trajectory (oracle (r:=r) lp flow G D k p b load F child) j)
  rounded : ∀ j,j<limit → ∀ a,
      oracle (r:=r) lp flow G D k p b load F child j
        (trajectory (oracle (r:=r) lp flow G D k p b load F child) j).2=.cut a →
      Bounds (2^w) c roundH v n j limit cfg.rounded extent
        (trajectory (oracle (r:=r) lp flow G D k p b load F child) j) a
  hcost : (16*(Lax109476.RationalEncoding.encodeProgram (MomentLP.program G k r)).length+
      (36*M.size+124)*MomentLP.dimension n r+135+callCost+2)+14+(193*MomentLP.dimension n r+48)+
      NativeNearExecution.timeBound cfg n r nearM S costH childTime flowTime+6≤oracleCost
  hround : ∀ j,j<limit → NativeRoundedUpdate.timeBound cfg.rounded c (MomentLP.dimension n r) roundH j+16≤roundCost

/-- The complete bounded search now runs through the concrete projection,
near, collection and update phases. There is no assumed Steps contract. -/
theorem search_segment {n r : ℕ} (D k p b load F fuel S v limit w M farM nearM costH T space
    oracleTime callCost flowTime childSteps childTime c roundH oracleCost roundCost precision : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lp flow : List ℕ → List ℕ) (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (data : Setup (r:=r) D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime
      childSteps childTime c roundH oracleCost roundCost cfg G lp flow extent front child)
    (hlimit : limit=RoundedOracleSearch.steps (MomentLP.dimension n r) precision)
    (σ : Env) (hc : Context (2^w) D k r p b load F fuel S v limit cfg G extent front σ)
    (hs : NativeRoundedTrace.StoredState 0 ((1,0) : State (MomentLP.dimension n r)) σ)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=4) :
    ∃ τ transitions total,Segment (2^w) (phases cfg) transitions total σ τ ∧
      transitions≤((childSteps+5)*(n+1)+7)*limit ∧ total≤(oracleCost+roundCost)*limit ∧
      Context (2^w) D k r p b load F fuel S v limit cfg G extent front τ ∧
      NativeRoundTrace.Stopped (search (oracle (r:=r) lp flow G D k p b load F child) precision) τ ∧ RootData σ τ := by
  have concrete := steps D k p b load F fuel S v limit w M farM nearM costH T space oracleTime callCost flowTime
    childSteps childTime c roundH oracleCost roundCost cfg G lp flow extent front child σ
    data.program data.setup data.rounded data.hcost data.hround
  have scan := NativeRoundTrace.search_segment (2^w) cfg
    (WithRoot σ (Context (2^w) D k r p b load F fuel S v limit cfg G extent front))
    (Invariant (WithRoot σ (Context (2^w) D k r p b load F fuel S v limit cfg G extent front))
      (oracle (r:=r) lp flow G D k p b load F child))
    (oracle (r:=r) lp flow G D k p b load F child) precision
    ((childSteps+5)*(n+1)+7) (oracleCost+roundCost) (by simpa only [←hlimit] using concrete)
    σ ⟨⟨hc,RootData.refl σ⟩,hs,rfl⟩ hr hp
  obtain ⟨τ,s,t,trace,hs,ht,⟨contextτ,rootτ⟩,answerτ⟩ := scan
  exact ⟨τ,s,t,trace,by simpa only [←hlimit] using hs,by simpa only [←hlimit] using ht,contextτ,answerτ,rootτ⟩

end Lax263307Proofs.NativeOracleRounds
