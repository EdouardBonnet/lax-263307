import Lax263307Proofs.NativeMachineSegment

namespace Lax263307Proofs.NativeMachineFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineSegment

/-- Any finite execution segment preserves a scalar absent from all
phase write footprints, including throughout nested child executions. -/
theorem scalar {B steps total : ℕ} {cases : List Com} {σ τ : Env}
    (trace : Segment B cases steps total σ τ) (s : String)
    (hs : ∀ c∈cases,s∉c.wvars) : τ.vars s=σ.vars s := by
  induction trace with
  | nil => rfl
  | step h j hj rr rest ih =>
    exact ih.trans (rr.frame_var s (hs _ (List.getElem_mem j.isLt)))

theorem array {B steps total : ℕ} {cases : List Com} {σ τ : Env}
    (trace : Segment B cases steps total σ τ) (a : String)
    (ha : ∀ c∈cases,a∉c.warrs) : τ.arrs a=σ.arrs a := by
  induction trace with
  | nil => rfl
  | step h j hj rr rest ih =>
    exact ih.trans (rr.frame_arr a (ha _ (List.getElem_mem j.isLt)))

/-- The lengths of all reserved buffers are invariant throughout a
segment, even when their contents are changed by child computations. -/
theorem array_length {B steps total : ℕ} {cases : List Com} {σ τ : Env}
    (trace : Segment B cases steps total σ τ) (a : String) : (τ.arrs a).length=(σ.arrs a).length := by
  induction trace with
  | nil => rfl
  | step h j hj rr rest ih =>
    exact ih.trans (Lax455465Proofs.RamFrames.run_array_length rr a)

/-- Recover the concrete handler run from a one-transition segment. This
lets callers frame arbitrary additional node invariants without expanding
the handler proof or assuming that every phase preserves those fields. -/
theorem single_run {B total : ℕ} {cases : List Com} {σ τ : Env}
    (trace : Segment B cases 1 total σ τ) (j : Fin cases.length)
    (hp : σ.vars "machine.phase"=j.val) : Run B cases[j.val] σ τ total := by
  cases trace with
  | step hr i hi rr rest =>
    cases rest with
    | nil =>
      have he : i=j := Fin.ext (hi.symm.trans hp)
      subst i
      simpa only [Nat.add_zero] using rr

theorem single_scalar {B total : ℕ} {cases : List Com} {σ τ : Env}
    (trace : Segment B cases 1 total σ τ) (j : Fin cases.length)
    (hp : σ.vars "machine.phase"=j.val) (s : String) (hs : s∉cases[j.val].wvars) :
    τ.vars s=σ.vars s := (single_run trace j hp).frame_var s hs

theorem single_array {B total : ℕ} {cases : List Com} {σ τ : Env}
    (trace : Segment B cases 1 total σ τ) (j : Fin cases.length)
    (hp : σ.vars "machine.phase"=j.val) (a : String) (ha : a∉cases[j.val].warrs) :
    τ.arrs a=σ.arrs a := (single_run trace j hp).frame_arr a ha

end Lax263307Proofs.NativeMachineFrame
