import Lax263307Proofs.NativeReturnTrace
import Lax263307Proofs.NativeCoreFrame

namespace Lax263307Proofs.NativeChildTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeCoreMachine NativeMachineSegment

/-- Phase 11 prepares the actual induced child graph and pushes the parent
snapshot with continuation 12 before entering the smaller-fuel node.
The snapshot run is retained for the complete parent-restoration theorem. -/
theorem call_segment {n : ℕ} (B S target fuel : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ) (C : Finset (Fin n))
    (front : List ℕ)
    (hB : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+n*n+n+target+fuel+23<B)
    (σ : Env) (hb : NativeStateBounds.Bounded B σ) (hd : NativeRestrictionRead.Data G x C σ)
    (hfront : Prefix front "recursion.frames" σ) (hwords : σ.vars "stack.words"=front.length)
    (hstride : σ.vars "recursion.stride"=S) (hext : ∀ a∈frameArrays cfg,(σ.arrs a).length=S)
    (hstack : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤(σ.arrs "recursion.frames").length)
    (hchild : C.card*C.card≤(σ.arrs "child.graph").length)
    (hsearch : C.card*C.card≤(σ.arrs "search.graph").length)
    (ht : σ.vars "component.target"=target) (hf : σ.vars "recursion.fuel"=fuel+1)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=11) :
    ∃ saved τ,Run B (.seq NativeChildGraph.command (go 12)) σ saved (36*(C.card*C.card)+12) ∧
      NativeStateBounds.Bounded B saved ∧ saved.vars "machine.running"=1 ∧ saved.vars "machine.phase"=12 ∧
      Segment B (phases cfg) 1
        ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(C.card*C.card)+36) σ τ ∧
      Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" τ ∧
      τ.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length ∧
      Prefix (NativeWeightReduction.adjacency (restriction G C)) "search.graph" τ ∧
      τ.vars "graph.n"=C.card ∧ τ.vars "node.k"=target ∧ τ.vars "recursion.fuel"=fuel ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=1 := by
  have hc : C.card≤n := NativeMaskUnpack.card_bound C
  have hsq : C.card*C.card≤n*n := Nat.mul_self_le_mul_self hc
  obtain ⟨ν,r1,p1⟩ := NativeChildGraph.command_spec B n G x C (by omega) σ ⟨hd,hchild⟩
  have hv : ∀ s∈frameScalars cfg,s∉["stack.i","stack.copy.length","stack.words"] := by
    intro s hs he
    apply scalar_not_saved cfg s _ hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl <;> decide
  obtain ⟨τ,r2,p2⟩ := NativeChildCall.command_spec B S C.card target fuel 1 12 (restriction G C)
    (frameArrays cfg) (frameScalars cfg) front (frames_not_saved cfg) hv (by omega) ν
    ⟨NativeStateBounds.run r1 hb,
      by simpa only [Prefix,r1.frame_arr "recursion.frames" (by decide)] using hfront,
      (r1.frame_var _ (by decide)).trans hwords,(r1.frame_var _ (by decide)).trans hstride,
      by intro a ha; rw [RamFrames.run_array_length r1]; exact hext a ha,
      by simpa only [RamFrames.run_array_length r1] using hstack,p1.2,p1.1.count,
      by simpa only [RamFrames.run_array_length r1] using hsearch,
      (r1.frame_var _ (by decide)).trans ht,(r1.frame_var _ (by decide)).trans hf⟩
  let saved := ν.setVar "machine.phase" 12
  have rsave : Run B (go 12) ν saved 2 := Run.assign (evalB_lit (show 12<B by omega))
  have snapshot : Run B (.seq NativeChildGraph.command (go 12)) σ saved (36*(C.card*C.card)+12) :=
    (r1.seq rsave).mono (by omega)
  have running1 : ν.vars "machine.running"=1 := (r1.frame_var _ (by decide)).trans hr
  have running2 : "machine.running"∉(NativeChildCall.command (frameArrays cfg) (frameScalars cfg) 1 12).wvars := by
    simp only [NativeChildCall.command,Com.wvars,List.mem_append,not_or]
    exact ⟨by decide,NativeChildCall.save_variable _ _ _ (by decide),by decide,by decide⟩
  have run : Run B (.seq NativeChildGraph.command (NativeChildCall.command (frameArrays cfg) (frameScalars cfg) 1 12)) σ τ
      ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(C.card*C.card)+36) :=
    (r1.seq r2).mono (by omega)
  exact ⟨saved,τ,snapshot,NativeStateBounds.run snapshot hb,(rsave.frame_var _ (by decide)).trans running1,
    by simp [saved],NativeMachineSegment.phase hr ⟨11,by change 11<16; decide⟩ hp run,
    p2.1,p2.2.1,p2.2.2.1,p2.2.2.2.1,p2.2.2.2.2.1,p2.2.2.2.2.2.1,
    (r2.frame_var _ running2).trans running1,p2.2.2.2.2.2.2⟩

end Lax263307Proofs.NativeChildTrace
