import Lax263307Proofs.NativeChildTrace

namespace Lax263307Proofs.NativeChildExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment

/-- Compose the actual call, the recursive induction-hypothesis segment,
and the actual return. Full parent restoration is a conclusion, with no
extra assumption that the child preserved the parent's working buffers. -/
theorem returned_segment {n : ℕ} (B S : ℕ) (cfg : Config)
    (front : List ℕ) (parent saved entry done : Env) (answer : Option (Finset (Fin n)))
    (callSteps callTime childSteps childTime prepTime : ℕ)
    (snapshot : Run B (.seq NativeChildGraph.command (go 12)) parent saved prepTime)
    (hsaved : NativeStateBounds.Bounded B saved)
    (hext : ∀ a∈frameArrays cfg,(saved.arrs a).length=S)
    (hB : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+2<B)
    (hr : saved.vars "machine.running"=1) (hp : saved.vars "machine.phase"=12)
    (call : Segment B (phases cfg) callSteps callTime parent entry)
    (recursive : Segment B (phases cfg) childSteps childTime entry done)
    (reply : NativeRoundTrace.Stopped answer done)
    (hstack : Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" done ∧
      done.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length ∧
      done.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length ∧ done.vars "recursion.stride"=S) :
    ∃ τ,Segment B (phases cfg) (callSteps+childSteps+1)
      (callTime+childTime+((16*S+16)*(frameArrays cfg).length+7*(frameScalars cfg).length+12)) parent τ ∧
      Prefix front "recursion.frames" τ ∧ τ.vars "stack.words"=front.length ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=12 ∧ NativeTargetDriver.Reply answer τ ∧
      (∀ s,s∉excludedScalars → τ.vars s=saved.vars s) ∧
      (∀ a,a≠"recursion.frames" → τ.arrs a=saved.arrs a) := by
  have before := NativeMachineSegment.append call recursive
  have extDone : ∀ a∈frameArrays cfg,(done.arrs a).length=S := by
    intro a ha
    have hlen := NativeMachineFrame.array_length before a
    have hprep := RamFrames.run_array_length snapshot a
    rw [hlen,←hprep]
    exact hext a ha
  obtain ⟨τ,ret,hfront,ha,hv,hwords,hr',hp',hreply⟩ := NativeReturnTrace.child_segment B S cfg front saved answer
    hsaved hext hB hr hp done reply ⟨hstack.1,hstack.2.1,hstack.2.2.1,hstack.2.2.2,extDone⟩
  have whole := NativeMachineSegment.append before ret
  have restored := NativeCoreFrame.parent_restored snapshot whole hv ha
  exact ⟨τ,whole,hfront,hwords,hr',hp',hreply,restored⟩

end Lax263307Proofs.NativeChildExecution
