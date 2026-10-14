import Lax263307Proofs.NativeMachineTrace

namespace Lax263307Proofs.NativeMachineSegment

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMachineTrace

/-- A finite sequence of phase transitions that may stop at a parent
continuation rather than halting the whole machine. -/
inductive Segment (B : ℕ) (cases : List Com) : ℕ → ℕ → Env → Env → Prop
  | nil (σ : Env) : Segment B cases 0 0 σ σ
  | step {σ μ τ : Env} {steps total cost : ℕ} (h : σ.vars "machine.running"=1)
      (j : Fin cases.length) (hj : σ.vars "machine.phase"=j.val)
      (rr : Run B cases[j.val] σ μ cost) (rest : Segment B cases steps total μ τ) :
      Segment B cases (steps+1) (cost+total) σ τ

theorem append {B s t s' t' : ℕ} {cases : List Com} {σ μ τ : Env}
    (a : Segment B cases s t σ μ) (b : Segment B cases s' t' μ τ) :
    Segment B cases (s+s') (t+t') σ τ := by
  induction a with
  | nil => simpa only [Nat.zero_add] using b
  | step h j hj rr rest ih =>
    simpa only [Nat.add_assoc,Nat.add_comm 1,Nat.add_left_comm] using Segment.step h j hj rr (ih b)

theorem attach_trace {B s t s' t' : ℕ} {cases : List Com} {σ μ τ : Env}
    (a : Segment B cases s t σ μ) (b : Trace B cases s' t' μ τ) :
    Trace B cases (s+s') (t+t') σ τ := by
  induction a with
  | nil => simpa only [Nat.zero_add] using b
  | step h j hj rr rest ih =>
    simpa only [Nat.add_assoc,Nat.add_comm 1,Nat.add_left_comm] using Trace.step h j hj rr (ih b)

theorem finish {B s t : ℕ} {cases : List Com} {σ τ : Env}
    (a : Segment B cases s t σ τ) (halt : τ.vars "machine.running"=0) :
    Trace B cases s t σ τ := by
  simpa only [Nat.add_zero] using attach_trace a (Trace.stop halt)

theorem phase {B K : ℕ} {cases : List Com} {σ τ : Env}
    (running : σ.vars "machine.running"=1) (j : Fin cases.length)
    (phase : σ.vars "machine.phase"=j.val) (rr : Run B cases[j.val] σ τ K) :
    Segment B cases 1 K σ τ := by
  simpa only [Nat.zero_add,Nat.add_zero] using Segment.step running j phase rr (Segment.nil τ)

/-- Glue independently checked node, child-call, and return segments,
then obtain the concrete execution bound of the fixed dispatcher. -/
theorem driver_run {B s t : ℕ} {cases : List Com} {σ τ : Env}
    (a : Segment B cases s t σ τ) (halt : τ.vars "machine.running"=0)
    (hB : cases.length+2<B) :
    Run B (driver cases) σ τ (t+(4*cases.length+4)*s+4) :=
  NativeMachineTrace.driver_run (finish a halt) hB

end Lax263307Proofs.NativeMachineSegment
