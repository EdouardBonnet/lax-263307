import Lax263307Proofs.NativeNodeExecution
import Lax263307Proofs.NativeRootTrace

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCoreExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeOracleContext NativeNodeProtocol

def Root {n : ℕ} (B D S v : ℕ) (cfg : Config) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (extent : String → ℕ) (σ : Env) : Prop :=
  Protocol B D S v cfg extent [] σ ∧ GraphData G σ

theorem frame {n B D S v t : ℕ} {cfg : Config} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {extent : String → ℕ} {σ τ : Env} {c : Com} (rr : Run B c σ τ t)
    (hq : Root B D S v cfg G extent σ)
    (hv : ∀ s∈NativeNodeProtocol.scalars,s∉c.wvars)
    (hn : "graph.n"∉c.wvars) (hs : "recursion.frames"∉c.warrs) (hg : "search.graph"∉c.warrs) :
    Root B D S v cfg G extent τ :=
  ⟨NativeNodeProtocol.frame rr hq.1 hv hs,(rr.frame_var _ hn).trans hq.2.1,
    by simpa only [Prefix,rr.frame_arr "search.graph" hg] using hq.2.2⟩

theorem stable {n B D S v : ℕ} (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent : String → ℕ) : NativeRootTrace.RootStable B (Root B D S v cfg G extent) := by
  intro σ τ t c hc rr hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl <;> exact frame rr hq (by decide) (by decide) (by decide) (by decide)

/-- Complete node executions supply the actual phase-15 root attempts;
the actual stack-empty return phase is included in their time bound. -/
theorem attempts {n : ℕ} (D fuel S v w nodeSteps nodeTime : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lp flow : List ℕ → List ℕ)
    (extent : String → ℕ) (eligible : Eligible) (hB : 16<2^w)
    (hroot : ∀ k,0<k → k≤n → eligible fuel n G k 0)
    (execution : Executes (2^w) D fuel S v nodeSteps nodeTime cfg lp flow extent eligible) :
    NativeRootTrace.Attempts (2^w) cfg (Root (2^w) D S v cfg G extent)
      (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G) fuel (nodeSteps+1) (nodeTime+6) := by
  intro k hk hkn σ hq htarget hdepth hrt hrf hr hp
  obtain ⟨μ,s,t,first,hs,ht,answer,protocolμ,rootμ,graphμ⟩ := execution n G k [] σ (hroot k hk hkn)
    ⟨hq.1,hq.2.1,hq.2.2,htarget,hdepth⟩ hr hp
  obtain ⟨τ,last,eqτ,runningτ,phaseτ,replyτ⟩ := NativeReturnTrace.root_segment (2^w) cfg
    (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) hB μ
    (by simpa using protocolμ.cursor) answer
  have rr : Run (2^w) (go 15) μ τ 2 := by
    rw [eqτ]
    exact Run.assign (evalB_lit (by omega))
  have rootτ := rootμ.trans (root_frame rr (by decide) (by decide))
  exact ⟨τ,s+1,t+6,NativeMachineSegment.append first last,by omega,by omega,
    frame rr ⟨protocolμ,graphμ⟩ (by decide) (by decide) (by decide) (by decide),
    rootτ.1.trans hrt,rootτ.2.trans hrf,runningτ,phaseτ,replyτ⟩

structure Input {n : ℕ} (B D fuel S v : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent : String → ℕ) (σ : Env) : Prop where
  bounded : NativeStateBounds.Bounded B σ
  graph : GraphData G σ
  accuracy : σ.vars "node.D"=D
  fuel : σ.vars "recursion.fuel"=fuel
  stride : σ.vars "recursion.stride"=S
  width : σ.vars "algorithm.roundWidth"=v
  lengths : ∀ a,(σ.arrs a).length=extent a

/-- The complete unweighted core command: frame-size calculation, actual
root initialization, all recursively executed attempts, and descending
target search. The only remaining premise is the numerical resource data. -/
theorem command_spec {n : ℕ} (D fuel S v w localSteps localTime branches : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lp flow : List ℕ → List ℕ)
    (extent : String → ℕ) (eligible : Eligible)
    (resources : NativeNodeExecution.Resources D S v w localSteps localTime branches cfg lp flow extent eligible)
    (hroot : ∀ k,0<k → k≤n → eligible fuel n G k 0)
    (hframe : S*(frameArrays cfg).length+(frameScalars cfg).length+S+(frameArrays cfg).length+10<2^w)
    (hB : n+fuel+20<2^w) (hm : 2^n<2^w) :
    let NS := NativeRecursionBudget.work localSteps branches fuel
    let NT := NativeRecursionBudget.work localTime branches fuel
    Spec (2^w) (Input (2^w) D fuel S v G extent) (NativeCoreMachine.command cfg)
      (fun _ τ => Root (2^w) D S v cfg G extent τ ∧
        NativeRootTrace.Answer (TargetSearch.search (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G) n) τ)
      ((NT+26+68*(NS+3))*n+98) := by
  dsimp only
  let NS := NativeRecursionBudget.work localSteps branches fuel
  let NT := NativeRecursionBudget.work localTime branches fuel
  have runs := NativeNodeExecution.executes D S v w localSteps localTime branches cfg lp flow extent eligible resources fuel
  have attempts := attempts D fuel S v w NS NT cfg G lp flow extent eligible (by omega) hroot runs
  have driver := NativeRootTrace.driver_spec (2^w) cfg (Root (2^w) D S v cfg G extent)
    (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G) fuel (NS+1) (NT+6) hB hm (stable cfg G extent) attempts
  intro σ hi
  obtain ⟨ν,r1,frameν⟩ := NativeRootTransitions.frame_size_spec (2^w) S cfg hframe σ hi.stride
  obtain ⟨μ,r2,initμ⟩ := NativeRootTransitions.initialize_spec (2^w) n fuel (by omega) ν
    ⟨(r1.frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.graph.1,(r1.frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.fuel⟩
  have qμ : Root (2^w) D S v cfg G extent μ := by
    refine ⟨⟨NativeStateBounds.run (r1.seq r2) hi.bounded,?_,by simp [Prefix],by simpa using initμ.2.2.1,
      ((r1.seq r2).frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.stride,(r2.frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans frameν,
      ((r1.seq r2).frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.width,
      ((r1.seq r2).frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.accuracy⟩,
      ((r1.seq r2).frame_var _ (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])).trans hi.graph.1,?_⟩
    · intro a; rw [RamFrames.run_array_length (r1.seq r2)]; exact hi.lengths a
    · simpa only [Prefix,(r1.seq r2).frame_arr "search.graph" (by simp [frameSize,initializeRoot,go,Com.wvars,Com.warrs])] using hi.graph.2
  obtain ⟨τ,r3,post⟩ := driver μ ⟨qμ,initμ.1,initμ.2.1,initμ.2.2.2.1,initμ.2.2.2.2⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono ?_,post⟩
  dsimp only [NS,NT]
  ring_nf
  omega

end Lax263307Proofs.NativeCoreExecution
