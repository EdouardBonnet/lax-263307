import Lax263307Proofs.NativeRoundTrace

namespace Lax263307Proofs.NativeReturnTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment

theorem reply_transfer {n : ℕ} (answer : Option (Finset (Fin n))) {σ τ : Env}
    (ht : τ.vars "recursion.return.tag"=σ.vars "recursion.return.tag")
    (hm : τ.vars "recursion.return.mask"=σ.vars "recursion.return.mask")
    (h : NativeTargetDriver.Reply answer σ) : NativeTargetDriver.Reply answer τ := by
  cases answer <;> simp only [NativeTargetDriver.Reply,ht,hm] at * <;> assumption

/-- The root node's return phase enters the target-search reply phase,
preserving every other scalar and all arrays. -/
theorem root_segment {n : ℕ} (B : ℕ) (cfg : Config) (answer : Option (Finset (Fin n)))
    (hB : 16<B) (σ : Env) (hs : σ.vars "stack.words"=0) (h : NativeRoundTrace.Stopped answer σ) :
    ∃ τ, Segment B (phases cfg) 1 6 σ τ ∧ τ=σ.setVar "machine.phase" 15 ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=15 ∧ NativeTargetDriver.Reply answer τ := by
  obtain ⟨τ,rr,po⟩ := NativeStackReturn.root_spec B 15 (frameArrays cfg) (frameScalars cfg) hB σ hs
  refine ⟨τ,NativeMachineSegment.phase h.1 ⟨14,by change 14<16; decide⟩ h.2.1 rr,
    po.2.2.2,?_,po.1,reply_transfer answer po.2.1 po.2.2.1 h.2.2⟩
  rw [po.2.2.2]
  simpa using h.1

/-- The child return phase restores the concrete parent continuation and
the whole saved working state while retaining the child's answer. -/
theorem child_segment {n : ℕ} (B S : ℕ) (cfg : Config)
    (front : List ℕ) (saved : Env) (answer : Option (Finset (Fin n)))
    (hsaved : NativeStateBounds.Bounded B saved)
    (hext : ∀ a∈frameArrays cfg,(saved.arrs a).length=S)
    (hB : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+2<B)
    (hr : saved.vars "machine.running"=1) (hp : saved.vars "machine.phase"=12)
    (σ : Env) (h : NativeRoundTrace.Stopped answer σ)
    (hs : Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" σ ∧
      σ.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length ∧
      σ.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length ∧ σ.vars "recursion.stride"=S ∧
      ∀ a∈frameArrays cfg,(σ.arrs a).length=S) :
    ∃ τ, Segment B (phases cfg) 1
      ((16*S+16)*(frameArrays cfg).length+7*(frameScalars cfg).length+12) σ τ ∧
      Prefix front "recursion.frames" τ ∧
      (∀ a∈frameArrays cfg,τ.arrs a=saved.arrs a) ∧
      (∀ s∈frameScalars cfg,τ.vars s=saved.vars s) ∧ τ.vars "stack.words"=front.length ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=12 ∧ NativeTargetDriver.Reply answer τ := by
  have hlen : 0<(frameScalars cfg).length := List.length_pos_of_mem (phase_saved cfg)
  obtain ⟨τ,rr,po⟩ := NativeStackReturn.child_spec B S 15 (frameArrays cfg) (frameScalars cfg) front saved
    (frames_not_saved cfg) (arrays_nodup cfg) (scalars_nodup cfg)
    (scalar_not_saved cfg _ (by decide)) (scalar_not_saved cfg _ (by decide))
    (scalar_not_saved cfg _ (by decide)) (scalar_not_saved cfg _ (by decide)) hsaved hext (by omega) hB σ hs
  exact ⟨τ,NativeMachineSegment.phase h.1 ⟨14,by change 14<16; decide⟩ h.2.1 rr,
    po.1,po.2.1,po.2.2.1,po.2.2.2.1,(po.2.2.1 _ (running_saved cfg)).trans hr,
    (po.2.2.1 _ (phase_saved cfg)).trans hp,
    reply_transfer answer po.2.2.2.2.1 po.2.2.2.2.2 h.2.2⟩

end Lax263307Proofs.NativeReturnTrace
