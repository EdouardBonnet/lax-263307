import Lax263307Proofs.NativeBlowUp

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeZeroScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def prefixOK (xs : List ℕ) (i : ℕ) : ℕ :=
  if (xs.take i).all (fun x => x==0) then 1 else 0

theorem prefix_ok_zero (xs : List ℕ) : prefixOK xs 0=1 := by simp [prefixOK]

theorem prefix_ok_le (xs : List ℕ) (i : ℕ) : prefixOK xs i≤1 := by
  unfold prefixOK
  split_ifs <;> omega

theorem prefix_ok_succ (xs : List ℕ) (i : ℕ) (hi : i<xs.length) :
    prefixOK xs (i+1)=if xs[i]=0 then prefixOK xs i else 0 := by
  unfold prefixOK
  rw [List.take_succ_eq_append_getElem hi,List.all_append]
  cases h : (xs.take i).all (fun x => x==0) <;> by_cases hx : xs[i]=0 <;> simp [hx]

theorem prefix_ok_full (xs : List ℕ) : prefixOK xs xs.length=1 ↔ ∀ x∈xs,x=0 := by
  simp [prefixOK,List.all_eq_true]

def update : Com := .seq
  (.ite (.eq (.var "test.bit") (.lit 0)) .skip (.assign "test.ok" (.lit 0)))
  (.assign "test.i" (.add (.var "test.i") (.lit 1)))

theorem update_spec (B i bit ok : ℕ) (hi : i+1<B) (hbit : bit<B) (_hok : ok≤1) (h1 : 1<B) :
    Spec B (fun σ => σ.vars "test.i"=i ∧ σ.vars "test.bit"=bit ∧ σ.vars "test.ok"=ok)
      update (fun _ τ => τ.vars "test.i"=i+1 ∧ τ.vars "test.ok"=if bit=0 then ok else 0) 10 := by
  by_cases hbit0 : bit=0
  · subst bit
    run_vcg
    all_goals simp_all [Env.setVar]
  · run_vcg
    all_goals simp_all [Env.setVar]

def body (read : Com) : Com := .seq read update

def command (read : Com) : Com := .seq (.assign "test.ok" (.lit 1))
  (.seq (.assign "test.i" (.lit 0)) (.while (.lt (.var "test.i") (.var "test.limit")) (body read)))

def Invariant (P : Env → Prop) (xs : List ℕ) (σ : Env) : Prop :=
  P σ ∧ σ.vars "test.limit"=xs.length ∧ σ.vars "test.i"≤xs.length ∧
  σ.vars "test.ok"=prefixOK xs (σ.vars "test.i")

theorem command_spec (B : ℕ) (xs : List ℕ) (P : Env → Prop) (read : Com) (K : ℕ)
    (hB : xs.length+2<B) (hwords : ∀ x∈xs,x<B)
    (hri : "test.i"∉read.wvars) (hrl : "test.limit"∉read.wvars) (hro : "test.ok"∉read.wvars)
    (hinit : ∀ σ,P σ → P ((σ.setVar "test.ok" 1).setVar "test.i" 0))
    (hupdate : ∀ σ τ,Run B update σ τ 10 → P σ → P τ)
    (hread : ∀ i (hi : i<xs.length), Spec B (fun σ => P σ ∧ σ.vars "test.i"=i) read
      (fun _ τ => P τ ∧ τ.vars "test.bit"=xs[i]) K) :
    Spec B (fun σ => P σ ∧ σ.vars "test.limit"=xs.length) (command read)
      (fun _ τ => P τ ∧ τ.vars "test.ok"=prefixOK xs xs.length)
      ((K+14)*xs.length+8) := by
  have h1 : 1<B := by omega
  have hbody : Spec B (fun σ => Invariant P xs σ ∧ σ.vars "test.i"<xs.length) (body read)
      (fun σ τ => Invariant P xs τ ∧ τ.vars "test.i"=σ.vars "test.i"+1) (K+10) := by
    rintro σ ⟨⟨hPσ,hlen,hle,hok⟩,hlt⟩
    let i := σ.vars "test.i"
    obtain ⟨ν,r1,p1⟩ := hread i hlt σ ⟨hPσ,rfl⟩
    have hiν : ν.vars "test.i"=i := r1.frame_var "test.i" hri
    have hokν : ν.vars "test.ok"=prefixOK xs i := (r1.frame_var "test.ok" hro).trans hok
    obtain ⟨τ,r2,p2⟩ := update_spec B i xs[i] (prefixOK xs i) (by dsimp [i]; omega)
      (hwords _ (List.getElem_mem hlt)) (prefix_ok_le xs i) h1 ν ⟨hiν,p1.2,hokν⟩
    have hPτ : P τ := hupdate ν τ r2 p1.1
    refine ⟨τ,r1.seq r2,⟨hPτ,?_,by rw [p2.1]; omega,?_⟩,p2.1⟩
    · exact (r2.frame_var "test.limit" (by decide)).trans ((r1.frame_var "test.limit" hrl).trans hlen)
    · rw [p2.1,prefix_ok_succ xs i hlt]
      exact p2.2
  have hloop := Spec.forRangeZero "test.i" "test.limit" (Invariant P xs) xs.length (K+10)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hPσ,hlen⟩
  let ν := σ.setVar "test.ok" 1
  have r1 : Run B (.assign "test.ok" (.lit 1)) σ ν 2 := Run.assign (evalB_lit h1)
  have hi : Invariant P xs (ν.setVar "test.i" 0) := by
    refine ⟨?_,?_,by simp,?_⟩
    · exact hinit σ hPσ
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hlen
    · simp [ν,prefix_ok_zero]
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by nlinarith),p2.1.1,?_⟩
  simpa only [p2.2] using p2.1.2.2.2

end Lax263307Proofs.NativeZeroScan
