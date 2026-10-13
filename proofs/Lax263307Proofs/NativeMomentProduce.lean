import Lax263307Proofs.NativeMomentAccess

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentProduce

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks NativeMomentRows

def Value (B : ℕ) (q : ℚ) (σ : Env) : Prop :=
  σ.vars "coefficient.positive"<B ∧ σ.vars "coefficient.negative"<B ∧
  ((σ.vars "coefficient.positive" : ℕ) : ℚ)-σ.vars "coefficient.negative"=q

def zeroCommand : Com := .seq (.assign "coefficient.positive" (.lit 0)) (.assign "coefficient.negative" (.lit 0))

theorem zero_spec (B : ℕ) (hB : 0<B) : Spec B (fun _ => True) zeroCommand (fun _ τ => Value B 0 τ) 4 := by
  run_vcg
  all_goals simp_all [Value,Env.setVar]

def singleCommand : Com := .seq (compare "coefficient.positive" "row.mask" "column.mask")
  (.assign "coefficient.negative" (.lit 0))

theorem single_spec {n : ℕ} (B : ℕ) (A J : Finset (Fin n)) (h1 : 1<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "row.mask"=mask A ∧ σ.vars "column.mask"=mask J)
      singleCommand (fun _ τ => Value B (same A J) τ) 8 := by
  rintro σ ⟨hA,hJ⟩
  obtain ⟨ν,r1,p1⟩ := compare_spec B (mask A) (mask J) "coefficient.positive" "row.mask" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) h1 σ ⟨hA,hJ⟩
  have hp : ν.vars "coefficient.positive"=same A J := by simpa only [same_masks] using p1
  let τ := ν.setVar "coefficient.negative" 0
  have r2 : Run B (.assign "coefficient.negative" (.lit 0)) ν τ 2 := Run.assign (evalB_lit (by omega))
  refine ⟨τ,r1.seq r2,?_,by simp [τ]; omega,?_⟩
  · simpa only [τ,vars_setVar,String.reduceEq,if_false,hp] using (same_le A J).trans_lt h1
  · simp only [τ,vars_setVar,String.reduceEq,if_false,if_true,hp,Nat.cast_zero,sub_zero]

theorem monotone_value_spec {n : ℕ} (B : ℕ) (A J : Finset (Fin n)) (v : Fin n) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "row.mask"=mask A ∧ σ.vars "column.mask"=mask J ∧ σ.vars "row.v"=v.val)
      monotoneCommand (fun _ τ => Value B ((same (insert v A) J : ℚ)-same A J) τ) 18 := by
  intro σ hσ
  obtain ⟨τ,rr,p⟩ := monotone_spec B A J v hB hm σ hσ
  refine ⟨τ,rr,?_,?_,?_⟩
  · rw [p.1]; exact (same_le _ _).trans_lt (by omega)
  · rw [p.2]; exact (same_le _ _).trans_lt (by omega)
  · rw [p.1,p.2]

theorem mass_value_spec {n : ℕ} (B : ℕ) (A J : Finset (Fin n)) (k : ℕ) (hB : n+2<B) (hk : k<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "row.mask"=mask A ∧ σ.vars "column.mask"=mask J ∧ σ.vars "row.k"=k)
      massCommand (fun _ τ => Value B ((matchCount A J n : ℚ)-(k*same A J : ℕ)) τ) (22*n+18) := by
  intro σ hσ
  obtain ⟨τ,rr,p⟩ := mass_spec B A J k hB hk hm σ hσ
  refine ⟨τ,rr,?_,?_,?_⟩
  · rw [p.1]; exact (matches_bound A J n).trans_lt (by omega)
  · rw [p.2]
    exact (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (same_le A J) : k*same A J≤k).trans_lt hk
  · rw [p.1,p.2]

def swap : Com := .seq (.assign "coefficient.temp" (.var "coefficient.positive"))
  (.seq (.assign "coefficient.positive" (.var "coefficient.negative"))
    (.assign "coefficient.negative" (.var "coefficient.temp")))

theorem swap_spec (B : ℕ) (q : ℚ) : Spec B (Value B q) swap (fun _ τ => Value B (-q) τ) 6 := by
  rintro σ ⟨hp,hn,hq⟩
  let ν := σ.setVar "coefficient.temp" (σ.vars "coefficient.positive")
  have r1 : Run B (.assign "coefficient.temp" (.var "coefficient.positive")) σ ν 2 := Run.assign (evalB_var hp)
  let μ := ν.setVar "coefficient.positive" (σ.vars "coefficient.negative")
  have r2 : Run B (.assign "coefficient.positive" (.var "coefficient.negative")) ν μ 2 := Run.assign (evalB_var hn)
  let τ := μ.setVar "coefficient.negative" (σ.vars "coefficient.positive")
  have r3 : Run B (.assign "coefficient.negative" (.var "coefficient.temp")) μ τ 2 := Run.assign (evalB_var hp)
  refine ⟨τ,r1.seq (r2.seq r3),hn,hp,?_⟩
  change (σ.vars "coefficient.negative" : ℚ)-σ.vars "coefficient.positive"=-q
  rw [←hq]
  ring

def guard (flag : String) (expected : ℕ) (c : Com) : Com :=
  .ite (.eq (.var flag) (.lit expected)) c zeroCommand

theorem guard_spec (B expected K : ℕ) (flag : String) (P : Env → Prop) (test : Prop) [Decidable test]
    (q : ℚ) (c : Com) (hB : 1<B) (hex : expected≤1)
    (hc : Spec B P c (fun _ τ => Value B q τ) K) :
    Spec B (fun σ => P σ ∧ σ.vars flag=if test then expected else 1-expected)
      (guard flag expected c) (fun _ τ => Value B (if test then q else 0) τ) (K+8) := by
  rintro σ ⟨hP,hflag⟩
  have heB : expected<B := hex.trans_lt hB
  have hnB : 1-expected<B := by omega
  by_cases h : test
  · have hf : σ.vars flag=expected := by simpa only [if_pos h] using hflag
    obtain ⟨τ,rr,p⟩ := hc σ hP
    have hb : (Cond.eq (.var flag) (.lit expected)).evalB B σ=some true := by
      have hh : (Cond.eq (.var flag) (.lit expected)).evalB B σ=some (expected==expected) := evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨hf.symm,hf ▸ heB⟩) (evalB_lit heB)
      simpa using hh
    exact ⟨τ,(Run.ite_true (d := zeroCommand) hb rr).mono (by simp [Cond.size,Expr.size]; omega),by simpa only [if_pos h] using p⟩
  · have hf : σ.vars flag=1-expected := by simpa only [if_neg h] using hflag
    obtain ⟨τ,rr,p⟩ := zero_spec B (by omega) σ trivial
    have hne : 1-expected≠expected := by omega
    have hb : (Cond.eq (.var flag) (.lit expected)).evalB B σ=some false := by
      have hh : (Cond.eq (.var flag) (.lit expected)).evalB B σ=some (1-expected==expected) := evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨hf.symm,hf ▸ hnB⟩) (evalB_lit heB)
      simpa only [beq_eq_false_iff_ne.mpr hne] using hh
    exact ⟨τ,(Run.ite_false (c := c) hb rr).mono (by simp [Cond.size,Expr.size]),by simpa only [if_neg h] using p⟩

end Lax263307Proofs.NativeMomentProduce
