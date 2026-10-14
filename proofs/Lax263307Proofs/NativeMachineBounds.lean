import Lax263307Proofs.NativeMachineSegment
import Lax263307Proofs.NativeStateBounds
import Lax263307Proofs.NativeArrayBounds

namespace Lax263307Proofs.NativeMachineBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning NativeMachineSegment

/-- Every finite controller segment preserves the true bounds of all
cells, buffers, and remaining input words, including nested child calls. -/
theorem state {B steps total : ℕ} {phases : List Com} {σ τ : Env}
    (trace : Segment B phases steps total σ τ) (hσ : NativeStateBounds.Bounded B σ) :
    NativeStateBounds.Bounded B τ := by
  induction trace with
  | nil => exact hσ
  | step hr j hj rr rest ih => exact ih (NativeStateBounds.run rr hσ)

theorem arrays {B steps total : ℕ} {phases : List Com} {σ τ : Env}
    (trace : Segment B phases steps total σ τ) (hσ : NativeArrayBounds.Bounded B σ) :
    NativeArrayBounds.Bounded B τ := by
  induction trace with
  | nil => exact hσ
  | step hr j hj rr rest ih => exact ih (NativeArrayBounds.run rr hσ)

end Lax263307Proofs.NativeMachineBounds
