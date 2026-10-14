import Lax263307Proofs.NativeRoundTrace
import Lax263307.RecursiveAlgorithm

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNodeTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters NativeCoreMachine NativeMachineSegment

def entryCost (a n : ℕ) : ℕ := 12*n.size+12*(2*n).size+12*(4*a+2)+88

/-- The actual entry and exhaustive phases return the functional algorithm's
answer, including the zero/one-vertex cases and targets larger than the graph. -/
theorem exhaustive_segment {n : ℕ} (B : ℕ) (cfg : Config) (lp flow : List ℕ → List ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D k fuel : ℕ)
    (hsmall : k≤cutoff cfg.a cfg.K cfg.b n D ∨ n≤1)
    (hdispatch : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+
      n+k+cutoff cfg.a cfg.K cfg.b n D+fuel+29<B)
    (hsearch : n*n+(n+1)*(k+1)+n+k+24<B) (hm : 2^n<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    ∀ σ, NativeNodeDispatch.Input n D k fuel σ →
      NativeSmallAttempt.Input G k σ → σ.vars "machine.running"=1 → σ.vars "machine.phase"=1 →
      ∃ τ, Segment B (phases cfg) 2
        (entryCost cfg.a n+NativeExhaustive.cost n k+15*n+20) σ τ ∧
        NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) τ ∧
        τ.vars "graph.n"=n ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" τ := by
  intro σ hinput hdata hr hp
  obtain ⟨ν,r1,p1⟩ := NativeNodeDispatch.command_spec B cfg.a cfg.K cfg.b n D k fuel 2 3 14
    (by omega) σ hinput
  have hrν : ν.vars "machine.running"=1 := (r1.frame_var _ (by
    change "machine.running"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars
    decide)).trans hr
  have hpν : ν.vars "machine.phase"=2 := by
    simpa only [NativeNodeDispatch.route,hsmall,if_true,NativeNodeDispatch.Output] using p1.2.1
  have hgν : Prefix (NativeWeightReduction.adjacency G) "search.graph" ν := by
    rw [Prefix,r1.frame_arr "search.graph" (by
      change "search.graph"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs
      decide)]
    exact hdata.2.2.1
  obtain ⟨τ,r2,p2⟩ := NativeSmallAttempt.command_spec B 14 G k hsearch hm hcoeff ν
    ⟨p1.1.1,p1.1.2.2.1,hgν,by rw [RamFrames.run_array_length r1]; exact hdata.2.2.2.1,
      by rw [RamFrames.run_array_length r1]; exact hdata.2.2.2.2⟩
  have s1 : Segment B (phases cfg) 1 (entryCost cfg.a n) σ ν :=
    NativeMachineSegment.phase hr ⟨1,by change 1<16; decide⟩ hp r1
  have s2 : Segment B (phases cfg) 1 (NativeExhaustive.cost n k+15*n+20) ν τ :=
    NativeMachineSegment.phase hrν ⟨2,by change 2<16; decide⟩ hpν r2
  refine ⟨τ,?_,?_,p2.1,?_⟩
  · convert NativeMachineSegment.append s1 s2 using 1 <;> simp [Nat.add_assoc]
  · refine ⟨(r2.frame_var _ (by decide)).trans hrν,p2.2.2,?_⟩
    cases fuel <;> simpa only [RecursiveAlgorithm.attempt,hsmall,if_true] using p2.2.1
  · rw [Prefix,r2.frame_arr "search.graph" (by decide)]
    exact hgν

/-- Impossible targets and exhausted recursion fuel return through the
actual rejection branch without invoking either external oracle. -/
theorem reject_segment {n : ℕ} (B : ℕ) (cfg : Config) (lp flow : List ℕ → List ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D k fuel : ℕ)
    (hsmall : ¬(k≤cutoff cfg.a cfg.K cfg.b n D ∨ n≤1)) (hreject : n<k ∨ fuel=0)
    (hdispatch : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+
      n+k+cutoff cfg.a cfg.K cfg.b n D+fuel+29<B) :
    ∀ σ, NativeNodeDispatch.Input n D k fuel σ →
      σ.vars "machine.running"=1 → σ.vars "machine.phase"=1 →
      ∃ τ, Segment B (phases cfg) 1 (entryCost cfg.a n) σ τ ∧
        NativeRoundTrace.Stopped (RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k) τ ∧
        NativeNodeDispatch.Input n D k fuel τ := by
  intro σ hi hr hp
  obtain ⟨τ,rr,po⟩ := NativeNodeDispatch.command_spec B cfg.a cfg.K cfg.b n D k fuel 2 3 14
    (by omega) σ hi
  have hout : τ.vars "machine.phase"=14 ∧ τ.vars "recursion.return.tag"=0 := by
    simpa only [NativeNodeDispatch.route,hsmall,if_false,hreject,if_true,NativeNodeDispatch.Output] using po.2.1
  refine ⟨τ,NativeMachineSegment.phase hr ⟨1,by change 1<16; decide⟩ hp rr,?_,po.1⟩
  refine ⟨(rr.frame_var _ (by
    change "machine.running"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars
    decide)).trans hr,hout.1,?_⟩
  have he : RecursiveAlgorithm.attempt lp flow cfg.a cfg.K cfg.b D fuel G k=none := by
    rcases hreject with hk | hf
    · cases fuel <;> simp only [RecursiveAlgorithm.attempt,hsmall,if_false,hk,if_true]
    · subst fuel
      simp only [RecursiveAlgorithm.attempt,hsmall,if_false]
      split <;> rfl
  simpa only [he,NativeTargetDriver.Reply] using hout.2

theorem large_input_frame {n B a K b D k t : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {c : Com} {σ τ : Env} (rr : Run B c σ τ t) (hi : NativeLargeNode.Input B a K b D k G σ)
    (hn : τ.vars "graph.n"=n) (hD : τ.vars "node.D"=D) (hk : τ.vars "node.k"=k)
    (hg : τ.arrs "search.graph"=σ.arrs "search.graph") : NativeLargeNode.Input B a K b D k G τ := by
  dsimp only [NativeLargeNode.Input] at hi ⊢
  rcases hi with ⟨_,_,_,graph,hb,ht,hbits,hm,hc,hi,hinput,hcache,hri,hs,hcenter⟩
  refine ⟨hn,hD,hk,?_,NativeArrayBounds.run rr hb,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Prefix,hg] using graph
  · simpa only [RamFrames.run_array_length rr] using ht
  · simpa only [RamFrames.run_array_length rr] using hbits
  · simpa only [RamFrames.run_array_length rr] using hm
  · simpa only [RamFrames.run_array_length rr] using hc
  · simpa only [RamFrames.run_array_length rr] using hi
  · simpa only [RamFrames.run_array_length rr] using hinput
  · simpa only [RamFrames.run_array_length rr] using hcache
  · simpa only [RamFrames.run_array_length rr] using hri
  · simpa only [RamFrames.run_array_length rr] using hs
  · simpa only [RamFrames.run_array_length rr] using hcenter

/-- The large-node entry branch reaches phase 3 with the exact graph,
target, accuracy and workspace preconditions needed by initialization. -/
theorem search_entry_segment {n : ℕ} (B : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D k fuel : ℕ)
    (hsmall : ¬(k≤cutoff cfg.a cfg.K cfg.b n D ∨ n≤1)) (hk : k≤n) (hf : 0<fuel)
    (hdispatch : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+
      n+k+cutoff cfg.a cfg.K cfg.b n D+fuel+29<B)
    (σ : Env) (hi : NativeLargeNode.Input B cfg.a cfg.K cfg.b D k G σ)
    (hfu : σ.vars "recursion.fuel"=fuel) (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=1) :
    ∃ τ, Segment B (phases cfg) 1 (entryCost cfg.a n) σ τ ∧
      NativeLargeNode.Input B cfg.a cfg.K cfg.b D k G τ ∧
      τ.vars "recursion.fuel"=fuel ∧ τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=3 := by
  obtain ⟨τ,rr,po⟩ := NativeNodeDispatch.command_spec B cfg.a cfg.K cfg.b n D k fuel 2 3 14
    (by omega) σ ⟨hi.1,hi.2.1,hi.2.2.1,hfu⟩
  refine ⟨τ,NativeMachineSegment.phase hr ⟨1,by change 1<16; decide⟩ hp rr,
    large_input_frame rr hi po.1.1 po.1.2.1 po.1.2.2.1 (rr.frame_arr _ (by
      change "search.graph"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs
      decide)),po.1.2.2.2,?_,?_⟩
  · exact (rr.frame_var _ (by
      change "machine.running"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars
      decide)).trans hr
  · have hrej : ¬(n<k ∨ fuel=0) := by omega
    simpa only [NativeNodeDispatch.route,hsmall,if_false,hrej,NativeNodeDispatch.Output] using po.2.1

/-- Phase 3 constructs the node's complete LP and catalog and initializes
the rounded state to (identity,zero), then reaches the first projection. -/
theorem large_segment {n : ℕ} (B : ℕ) (cfg : Config) (D k fuel : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 0<n) (hK : 0<cfg.K)
    (hparams : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+k+cfg.b+5<B)
    (hsetup : NativeMomentSetup.guardBound n k (level cfg.a cfg.K cfg.b n D)<B) (hm : 2^n<B)
    (hprec : NativeNodePrecision.guard n D (MomentLP.dimension n (level cfg.a cfg.K cfg.b n D))
      (floorDenominator cfg.a cfg.K cfg.b n D) (level cfg.a cfg.K cfg.b n D)<B)
    (hround : 3*(MomentLP.dimension n (level cfg.a cfg.K cfg.b n D)*MomentLP.dimension n (level cfg.a cfg.K cfg.b n D))+
      3*MomentLP.dimension n (level cfg.a cfg.K cfg.b n D)+20<B)
    (σ : Env) (hi : NativeLargeNode.Input B cfg.a cfg.K cfg.b D k G σ)
    (hfu : σ.vars "recursion.fuel"=fuel) (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=3) :
    ∃ τ,Segment B (phases cfg) 1 (NativeLargeNode.cost cfg.a n (level cfg.a cfg.K cfg.b n D)+2) σ τ ∧
      NativeLargeNode.Output cfg.a cfg.K cfg.b D k G τ ∧
      τ.vars "recursion.fuel"=fuel ∧ τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=4 := by
  obtain ⟨μ,r1,p1⟩ := NativeLargeNode.command_spec B cfg.a cfg.K cfg.b D k G hn hK hparams hsetup hm hprec hround σ hi
  let τ := μ.setVar "machine.phase" 4
  have r2 : Run B (go 4) μ τ 2 := Run.assign (evalB_lit (show 4<B by omega))
  refine ⟨τ,NativeMachineSegment.phase hr ⟨3,by change 3<16; decide⟩ hp (r1.seq r2),?_,?_,?_,by simp [τ]⟩
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [NativeNodeAliases.Output,τ,Env.setVar] using p1.1
    · exact NativeMomentFamily.data_frame G k _ r2
        (by intro s hs; simp only [NativeMomentFamily.fixedVars,List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl|rfl|rfl|rfl <;> decide)
        (by intro s hs; simp [go,Com.warrs]) p1.2.1
    · exact p1.2.2.1
    · simpa [τ,Env.setVar] using p1.2.2.2.1
    · simpa [NativeNodePrecision.Output,NativeNodePrecision.Context,τ,Env.setVar] using p1.2.2.2.2.1
    · exact p1.2.2.2.2.2.1
    · exact p1.2.2.2.2.2.2.1
    · simpa [τ,Env.setVar] using p1.2.2.2.2.2.2.2
  · exact (r2.frame_var _ (by decide)).trans ((r1.frame_var _ (by
      change "recursion.fuel"∉(NativeLargeNode.command 0 0 0).wvars
      decide)).trans hfu)
  · exact (r2.frame_var _ (by decide)).trans ((r1.frame_var _ (by
      change "machine.running"∉(NativeLargeNode.command 0 0 0).wvars
      decide)).trans hr)

end Lax263307Proofs.NativeNodeTrace
