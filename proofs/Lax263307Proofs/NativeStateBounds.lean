import Lax263307Proofs.NativeTabulate

namespace Lax263307Proofs.NativeStateBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def Bounded (B : ℕ) (σ : Env) : Prop :=
  (∀ s,σ.vars s<B) ∧ (∀ a z,z∈σ.arrs a → z<B) ∧ σ.InpBounded B

theorem set_var {B : ℕ} {σ : Env} (hd : Bounded B σ) (s : String) (v : ℕ) (hv : v<B) :
    Bounded B (σ.setVar s v) := by
  refine ⟨?_,hd.2.1,hd.2.2⟩
  intro t
  simp only [vars_setVar]
  split_ifs <;> first | exact hv | exact hd.1 t

theorem set_arr {B : ℕ} {σ : Env} (hd : Bounded B σ) (a : String) (i v : ℕ) (hv : v<B) :
    Bounded B (σ.setArr a i v) := by
  refine ⟨hd.1,?_,hd.2.2⟩
  intro b z hz
  simp only [arrs_setArr] at hz
  split_ifs at hz
  · rcases List.mem_or_eq_of_mem_set hz with hz | rfl
    · exact hd.2.1 a z hz
    · exact hv
  · exact hd.2.1 b z hz

/-- Every bounded source execution preserves a word bound on the entire
state, including scratch cells that can later be saved in recursion frames. -/
theorem big_step {B : ℕ} {c : Com} {σ τ : Env} {K : ℕ} (rr : BigStepB B c σ τ K)
    (hd : Bounded B σ) : Bounded B τ := by
  induction rr with
  | skip => exact hd
  | assign he => exact set_var hd _ _ (Expr.lt_of_evalB he)
  | store hi he hk => exact set_arr hd _ _ _ (Expr.lt_of_evalB he)
  | seq r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | ite_true hc rr ih => exact ih hd
  | ite_false hc rr ih => exact ih hd
  | while_true hc r1 r2 ih1 ih2 => exact ih2 (ih1 hd)
  | while_false hc => exact hd
  | read hh =>
    rename_i σ0 s v rest
    have hv := hd.2.2 _ (by rw [hh]; exact List.mem_cons_self)
    have hs := set_var hd s v hv
    refine ⟨hs.1,hs.2.1,?_⟩
    intro z hz
    exact hd.2.2 z (by rw [hh]; exact List.mem_cons_of_mem _ hz)
  | write he => exact ⟨hd.1,hd.2.1,hd.2.2⟩

theorem run {B : ℕ} {c : Com} {σ τ : Env} {K : ℕ} (rr : Run B c σ τ K)
    (hd : Bounded B σ) : Bounded B τ := by
  obtain ⟨_,_,rr⟩ := rr
  exact big_step rr hd

theorem initial {B : ℕ} (ext : String → ℕ) {xs : List ℕ} (hB : 0<B)
    (hx : ∀ z∈xs,z<B) : Bounded B (initEnv ext xs) := by
  refine ⟨fun _ => hB,?_,hx⟩
  intro a z hz
  have he : z=0 := (List.mem_replicate.mp hz).2
  simpa only [he] using hB

end Lax263307Proofs.NativeStateBounds
