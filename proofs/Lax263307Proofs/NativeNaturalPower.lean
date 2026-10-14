import Lax263307Proofs.NativeSignedSum

namespace Lax263307Proofs.NativeNaturalPower

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def Context (b e : ℕ) (σ : Env) : Prop := σ.vars "power.base"=b ∧ σ.vars "power.exponent"=e

def Invariant (b e : ℕ) (σ : Env) : Prop :=
  Context b e σ ∧ σ.vars "power.i"≤e ∧ σ.vars "power.value"=b^(σ.vars "power.i")

def step : Com := .seq (.assign "power.value" (.mul (.var "power.value") (.var "power.base")))
  (.assign "power.i" (.add (.var "power.i") (.lit 1)))

def command : Com := .seq (.assign "power.value" (.lit 1))
  (.seq (.assign "power.i" (.lit 0))
    (.while (.lt (.var "power.i") (.var "power.exponent")) step))

theorem step_spec (B b e i : ℕ) (hb : 1≤b) (hB : b+e+b^e+3<B) (hi : i<e) :
    Spec B (fun σ => Context b e σ ∧ σ.vars "power.i"=i ∧ σ.vars "power.value"=b^i) step
      (fun _ τ => Context b e τ ∧ τ.vars "power.i"=i+1 ∧ τ.vars "power.value"=b^(i+1)) 8 := by
  have hp : b^i<B := (Nat.pow_le_pow_right hb hi.le).trans_lt (by omega)
  have hnext : b^i*b<B := by
    rw [←pow_succ]
    exact (Nat.pow_le_pow_right hb hi).trans_lt (by omega)
  run_vcg
  all_goals simp_all [Context,pow_succ]
  all_goals omega

/-- Exact natural powering by a fixed multiplication loop. Intermediate
values are at most the final power for positive bases. -/
theorem command_spec (B b e : ℕ) (hb : 1≤b) (hB : b+e+b^e+3<B) :
    Spec B (Context b e) command
      (fun _ τ => Context b e τ ∧ τ.vars "power.value"=b^e) (12*e+8) := by
  have hbody : Spec B (fun σ => Invariant b e σ ∧ σ.vars "power.i"<e) step
      (fun σ τ => Invariant b e τ ∧ τ.vars "power.i"=σ.vars "power.i"+1) 8 := by
    rintro σ ⟨⟨hc,hle,hv⟩,hlt⟩
    obtain ⟨τ,rr,ht⟩ := step_spec B b e (σ.vars "power.i") hb hB hlt σ ⟨hc,rfl,hv⟩
    exact ⟨τ,rr,⟨ht.1,by rw [ht.2.1]; omega,by simpa only [ht.2.1] using ht.2.2⟩,ht.2.1⟩
  have hloop := Spec.forRangeZero "power.i" "power.exponent" (Invariant b e) e 8 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2) hbody
  intro σ hc
  let ν := σ.setVar "power.value" 1
  have r1 : Run B (.assign "power.value" (.lit 1)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hi : Invariant b e (ν.setVar "power.i" 0) := by
    refine ⟨?_,by simp,?_⟩
    · simpa only [Context,ν,vars_setVar,String.reduceEq,if_false] using hc
    · simp [ν]
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,by simpa only [p2.2] using p2.1.2.2⟩

end Lax263307Proofs.NativeNaturalPower
