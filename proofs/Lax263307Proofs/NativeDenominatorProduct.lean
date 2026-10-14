import Lax263307Proofs.NativeDenominatorData
import Lax263307Proofs.NativeCutRead

namespace Lax263307Proofs.NativeDenominatorProduct

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax263307.RationalCutBuffer NativeSignedArithmetic NativeDenominatorData NativeCutRead

def update : Com := .seq (.assign "cut.denominator" (.mul (.var "cut.denominator") (.var "rat.d")))
  (.assign "cut.i" (.add (.var "cut.i") (.lit 1)))

def step : Com := .seq NativeCutRead.command update

def command : Com := .seq (.assign "cut.denominator" (.lit 1))
  (.seq (.assign "cut.i" (.lit 0)) (.while (.lt (.var "cut.i") (.var "projection.n")) step))

def Invariant {n : ℕ} (a : Fin n → ℚ) (σ : Env) : Prop :=
  Context a σ ∧ σ.vars "cut.i"≤n ∧ σ.vars "cut.denominator"=partialProduct a (σ.vars "cut.i")

theorem update_spec (B n : ℕ) (a : Fin n → ℚ) (i : Fin n)
    (hs : n+2<B) (hD : denominator a<B) (hd : (a i).den<B) :
    Spec B (fun σ => σ.vars "cut.i"=i.val ∧ σ.vars "cut.denominator"=partialProduct a i.val ∧
      σ.vars "rat.d"=(a i).den) update
      (fun _ τ => τ.vars "cut.i"=i.val+1 ∧ τ.vars "cut.denominator"=partialProduct a (i.val+1)) 8 := by
  have hpart : partialProduct a i.val<B := (partial_le a i.val).trans_lt hD
  have hnext : partialProduct a i.val*(a i).den<B := by
    rw [←partial_step a i]
    exact (partial_le a (i.val+1)).trans_lt hD
  have hstep := partial_step a i
  run_vcg
  all_goals simp_all
  all_goals omega

/-- Multiply the actual encoded denominators in coordinate order. Every
partial product divides the final positive product and stays below its
word bound, including the empty vector whose product is one. -/
theorem command_spec (B M n : ℕ) (a : Fin n → ℚ)
    (hM : M<B) (hD : denominator a<B) (hs : 3*n+10<B) (ha : ∀ j,Bounded M (a j)) :
    Spec B (Context a) command
      (fun _ τ => Context a τ ∧ τ.vars "cut.denominator"=denominator a) (33*n+8) := by
  have h1 : 1<B := by omega
  have hbody : Spec B (fun σ => Invariant a σ ∧ σ.vars "cut.i"<n) step
      (fun σ τ => Invariant a τ ∧ τ.vars "cut.i"=σ.vars "cut.i"+1) 29 := by
    rintro σ ⟨⟨hc,hi,hprod⟩,hlt⟩
    let i : Fin n := ⟨σ.vars "cut.i",hlt⟩
    obtain ⟨ν,r1,p1⟩ := NativeCutRead.command_spec B M n a i hM hs ha σ ⟨hc,rfl⟩
    obtain ⟨τ,r2,p2⟩ := update_spec B n a i (by omega) hD ((ha i).2.trans_lt hM) ν
      ⟨r1.frame_var "cut.i" (by decide),(r1.frame_var "cut.denominator" (by decide)).trans hprod,p1.2.2.2.1⟩
    have rr := r1.seq r2
    refine ⟨τ,rr,⟨?_,by rw [p2.1]; exact i.isLt,?_⟩,p2.1⟩
    · simpa only [Context,Prefix,r2.frame_arr "cut.source" (by decide),r2.frame_var "projection.n" (by decide)] using p1.1
    · simpa only [p2.1] using p2.2
  have hloop := Spec.forRangeZero "cut.i" "projection.n" (Invariant a) n 29 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2) hbody
  intro σ hc
  let ν := σ.setVar "cut.denominator" 1
  have r1 : Run B (.assign "cut.denominator" (.lit 1)) σ ν 2 := Run.assign (evalB_lit h1)
  have hinit : Invariant a (ν.setVar "cut.i" 0) := by
    refine ⟨?_,by simp,?_⟩
    · simpa only [ν,Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hc
    · simp [ν,partialProduct,product]
  obtain ⟨τ,r2,p2⟩ := hloop ν hinit
  refine ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,?_⟩
  simpa only [p2.2,full_product] using p2.1.2.2

end Lax263307Proofs.NativeDenominatorProduct
