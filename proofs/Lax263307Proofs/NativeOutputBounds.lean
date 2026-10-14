import Lax263307Proofs.NativeStateBounds

namespace Lax263307Proofs.NativeOutputBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Every emitted value inherits the bound of the actual command run. -/
theorem big_step {B : ℕ} {c : Com} {σ τ : Env} {K : ℕ} (rr : BigStepB B c σ τ K)
    (hd : ∀ v∈σ.out,v<B) : ∀ v∈τ.out,v<B := by
  induction rr with
  | skip => exact hd
  | assign he => exact hd
  | store hi he hk => exact hd
  | seq r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | ite_true hc rr ih => exact ih hd
  | ite_false hc rr ih => exact ih hd
  | while_true hc r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | while_false hc => exact hd
  | read hh => exact hd
  | write he =>
    intro v hv
    simp only [List.mem_append,List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hd v hv
    · exact Expr.lt_of_evalB he

theorem run {B : ℕ} {c : Com} {σ τ : Env} {K : ℕ} (rr : Run B c σ τ K)
    (hd : ∀ v∈σ.out,v<B) : ∀ v∈τ.out,v<B := by
  obtain ⟨_,_,rr⟩ := rr
  exact big_step rr hd

end Lax263307Proofs.NativeOutputBounds
