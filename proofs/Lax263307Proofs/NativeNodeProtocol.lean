import Lax263307Proofs.NativeOracleContext
import Lax263307Proofs.NativeNodeTrace

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNodeProtocol

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeOracleContext

def scalars : List String := ["stack.words","recursion.stride","frame.length","algorithm.roundWidth","node.D"]

theorem frame {B D S v t : ℕ} {cfg : Config} {extent : String → ℕ} {front : List ℕ}
    {c : Com} {σ τ : Env} (rr : Run B c σ τ t) (hc : Protocol B D S v cfg extent front σ)
    (hv : ∀ s∈scalars,s∉c.wvars) (ha : "recursion.frames"∉c.warrs) :
    Protocol B D S v cfg extent front τ := by
  refine ⟨NativeStateBounds.run rr hc.bounded,?_,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.cursor,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.stride,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.frameLength,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.roundWidth,
    (rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.accuracy⟩
  · intro a; rw [RamFrames.run_array_length rr]; exact hc.lengths a
  · simpa only [Prefix,rr.frame_arr "recursion.frames" ha] using hc.stack

theorem dispatch_frame {B D S v t : ℕ} (cfg : Config) {extent : String → ℕ} {front : List ℕ}
    {σ τ : Env} (rr : Run B (NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14) σ τ t)
    (hc : Protocol B D S v cfg extent front σ) : Protocol B D S v cfg extent front τ := by
  apply frame rr hc
  · change ∀ s∈scalars,s∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars
    decide
  · change "recursion.frames"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs
    decide

theorem large_frame {B D S v t : ℕ} (cfg : Config) {extent : String → ℕ} {front : List ℕ}
    {σ τ : Env} (rr : Run B (.seq (NativeLargeNode.command cfg.a cfg.K cfg.b) (go 4)) σ τ t)
    (hc : Protocol B D S v cfg extent front σ) : Protocol B D S v cfg extent front τ := by
  apply frame rr hc
  · change ∀ s∈scalars,s∉(Com.seq (NativeLargeNode.command 0 0 0) (go 4)).wvars
    decide
  · change "recursion.frames"∉(Com.seq (NativeLargeNode.command 0 0 0) (go 4)).warrs
    decide

theorem dispatch_root {B t : ℕ} (cfg : Config) {σ τ : Env}
    (rr : Run B (NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14) σ τ t) : RootData σ τ := by
  apply root_frame rr
  all_goals first
    | change "root.target"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars; decide
    | change "root.fuel"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars; decide

theorem large_root {B t : ℕ} (cfg : Config) {σ τ : Env}
    (rr : Run B (.seq (NativeLargeNode.command cfg.a cfg.K cfg.b) (go 4)) σ τ t) : RootData σ τ := by
  apply root_frame rr
  all_goals first
    | change "root.target"∉(Com.seq (NativeLargeNode.command 0 0 0) (go 4)).wvars; decide
    | change "root.fuel"∉(Com.seq (NativeLargeNode.command 0 0 0) (go 4)).wvars; decide

theorem child_variable (cfg : Config) (s : String)
    (hg : s∉NativeChildGraph.command.wvars) (hc : s∉NativeChildActivate.command.wvars)
    (he : s∉(NativeChildCall.enter 1).wvars) (hphase : s≠"machine.phase")
    (hstack : s∉["stack.i","stack.copy.length","stack.words"]) :
    s∉((phases cfg)[11]'(by change 11<16; decide)).wvars := by
  have hsave := NativeChildCall.save_variable (frameArrays cfg) (frameScalars cfg) s hstack
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeChildCall.command,go,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or,not_false_eq_true]

theorem pushed_length {B D S v t : ℕ} {cfg : Config} {extent : String → ℕ} {front : List ℕ}
    {σ saved : Env} {c : Com} (rr : Run B c σ saved t)
    (hc : Protocol B D S v cfg extent front σ) (hext : ∀ a∈frameArrays cfg,extent a=S) :
    (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved).length=
      front.length+S*(frameArrays cfg).length+(frameScalars cfg).length := by
  have h : (NativeFrameBuffers.words (frameArrays cfg) saved).length=S*(frameArrays cfg).length :=
    NativeFrameBuffers.words_length _ S saved (fun a ha => by rw [RamFrames.run_array_length rr,hc.lengths]; exact hext a ha)
  simp only [List.length_append,NativeRecursionFrame.words,NativeFrameScalars.words,List.length_map,h,Nat.add_assoc]

/-- The actual phase-11 call inherits the fixed width, accuracy and frame
size. The stack prefix/cursor are the actual pushed values from that call. -/
theorem child_entry {B D S v t cost : ℕ} (cfg : Config) {extent : String → ℕ} {front : List ℕ}
    {σ saved entry : Env} {c : Com} (snapshot : Run B c σ saved t)
    (call : Segment B (phases cfg) 1 cost σ entry)
    (hc : Protocol B D S v cfg extent front σ) (hext : ∀ a∈frameArrays cfg,extent a=S)
    (hp : σ.vars "machine.phase"=11)
    (hfront : Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" entry)
    (hwords : entry.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length) :
    Protocol B D S v cfg extent
      (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) entry := by
  have rr := NativeMachineFrame.single_run call ⟨11,by change 11<16; decide⟩ hp
  refine ⟨NativeMachineBounds.state call hc.bounded,?_,hfront,?_,?_,?_,?_,?_⟩
  · intro a; rw [NativeMachineFrame.array_length call]; exact hc.lengths a
  · rw [pushed_length snapshot hc hext]; exact hwords
  all_goals apply (rr.frame_var _ (child_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide))).trans
  all_goals first | exact hc.stride | exact hc.frameLength | exact hc.roundWidth | exact hc.accuracy

abbrev Eligible := (fuel n : ℕ) → SimpleGraph (Fin n) → ℕ → ℕ → Prop

def GraphData {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ

structure Input {n : ℕ} (B D fuel S v : ℕ) (cfg : Config) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (k : ℕ) (extent : String → ℕ) (front : List ℕ) (σ : Env) : Prop where
  protocol : Protocol B D S v cfg extent front σ
  order : σ.vars "graph.n"=n
  graph : Prefix (NativeWeightReduction.adjacency G) "search.graph" σ
  target : σ.vars "node.k"=k
  depth : σ.vars "recursion.fuel"=fuel

def Executes (B D fuel S v steps time : ℕ) (cfg : Config) (lp flow : List ℕ → List ℕ)
    (extent : String → ℕ) (eligible : Eligible) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] k (front : List ℕ) σ,
    eligible fuel n G k front.length → Input B D fuel S v cfg G k extent front σ →
    σ.vars "machine.running"=1 → σ.vars "machine.phase"=1 →
    ∃ τ s t,Segment B (phases cfg) s t σ τ ∧ s≤steps ∧ t≤time ∧
      NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) τ ∧
      Protocol B D S v cfg extent front τ ∧ RootData σ τ ∧ GraphData G τ

def Children {n : ℕ} (B D fuel S v childSteps childTime : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (extent : String → ℕ) (front : List ℕ)
    (eligible : Eligible) (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) : Prop :=
  ∀ C target σ,eligible fuel C.card (ComputedSeparators.restriction G C) target
      (front.length+S*(frameArrays cfg).length+(frameScalars cfg).length) →
    Protocol B D S v cfg extent front σ → σ.vars "machine.phase"=11 →
    NativeCollectionChild.Recursive B S fuel childSteps childTime cfg G C target front σ (child C target)

/-- The smaller-fuel node induction hypothesis discharges the actual
child-execution premise, including the pushed stack and fixed frame data. -/
theorem children {n : ℕ} (B D fuel S v childSteps childTime : ℕ) (cfg : Config)
    (lp flow : List ℕ → List ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent : String → ℕ) (front : List ℕ) (eligible : Eligible)
    (hext : ∀ a∈frameArrays cfg,extent a=S)
    (ih : Executes B D fuel S v childSteps childTime cfg lp flow extent eligible) :
    Children B D fuel S v childSteps childTime cfg G extent front eligible
      (fun C t => RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel (ComputedSeparators.restriction G C) t) := by
  intro C target σ hel hp phase saved entry snapshot call hfront hwords hgraph horder hk hf hr he
  have protocolEntry := child_entry cfg snapshot call hp hext phase hfront hwords
  have hlength := pushed_length snapshot hp hext
  obtain ⟨τ,s,t,trace,hs,ht,answer,protocolDone,rootDone,graphDone⟩ := ih C.card (ComputedSeparators.restriction G C) target
    (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) entry
    (by simpa only [hlength] using hel) ⟨protocolEntry,horder,hgraph,hk,hf⟩ hr he
  exact ⟨τ,s,t,trace,hs,ht,answer,protocolDone.stack,
    by simpa only [hlength] using protocolDone.cursor,protocolDone.frameLength,protocolDone.stride⟩

end Lax263307Proofs.NativeNodeProtocol
