import Lax263307Proofs.NativeMomentFamily

namespace Lax263307Proofs.NativeArrayBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Bounded (B : ℕ) (σ : Env) : Prop := ∀ a,∀ z ∈ σ.arrs a,z < B

theorem big_step {B K : ℕ} {c : Com} {σ τ : Env} (rr : BigStepB B c σ τ K)
    (hb : Bounded B σ) : Bounded B τ := by
  induction rr with
  | skip => exact hb
  | assign _ => exact hb
  | store hi he hj =>
    intro a z hz
    simp only [arrs_setArr] at hz
    split_ifs at hz with h
    · obtain hz|rfl := List.mem_or_eq_of_mem_set hz
      · exact hb _ _ hz
      · exact Expr.lt_of_evalB he
    · exact hb _ _ hz
  | seq _ _ ih ih' => exact ih' (ih hb)
  | ite_true _ _ ih => exact ih hb
  | ite_false _ _ ih => exact ih hb
  | while_true _ _ _ ih ih' => exact ih' (ih hb)
  | while_false _ => exact hb
  | read _ => exact hb
  | write _ => exact hb

theorem run {B K : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    (hb : Bounded B σ) : Bounded B τ := by
  obtain ⟨_,_,h⟩ := rr
  exact big_step h hb

theorem prefix_words {B : ℕ} {σ : Env} {xs : List ℕ} {a : String} (hb : Bounded B σ)
    (hp : Prefix xs a σ) : ∀ z ∈ xs,z < B := by
  intro z hz
  obtain ⟨i,hi,hz⟩ := List.getElem_of_mem hz
  have he := hp i hi
  rw [hz] at he
  exact hb a z (List.mem_of_getElem? he)

end Lax263307Proofs.NativeArrayBounds
