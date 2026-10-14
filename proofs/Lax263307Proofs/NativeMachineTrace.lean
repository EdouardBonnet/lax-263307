import Lax263307Proofs.NativeTabulate

namespace Lax263307Proofs.NativeMachineTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def dispatch : List Com → ℕ → Com
  | [],_ => .assign "machine.running" (.lit 0)
  | c::cs,i => .ite (.eq (.var "machine.phase") (.lit i)) c (dispatch cs (i+1))

def driver (cases : List Com) : Com := .while (.eq (.var "machine.running") (.lit 1)) (dispatch cases 0)

theorem while_true_run {B K K' : ℕ} {b : Cond} {c : Com} {σ μ τ : Env}
    (hc : b.evalB B σ=some true) (r1 : Run B c σ μ K) (r2 : Run B (.while b c) μ τ K') :
    Run B (.while b c) σ τ (1+b.size+K+K') := by
  obtain ⟨k,hk,rr1⟩ := r1
  obtain ⟨k',hk',rr2⟩ := r2
  exact ⟨_,by omega,BigStepB.while_true hc rr1 rr2⟩

/-- A finite execution trace of the fixed phase handlers. Recursive
calls are represented by changes to the saved machine state, so the
source syntax itself contains no recursively expanded program. -/
inductive Trace (B : ℕ) (cases : List Com) : ℕ → ℕ → Env → Env → Prop
  | stop {σ : Env} (h : σ.vars "machine.running"=0) : Trace B cases 0 0 σ σ
  | step {σ μ τ : Env} {steps total cost : ℕ} (h : σ.vars "machine.running"=1)
      (j : Fin cases.length) (hj : σ.vars "machine.phase"=j.val)
      (rr : Run B cases[j.val] σ μ cost) (rest : Trace B cases steps total μ τ) :
      Trace B cases (steps+1) (cost+total) σ τ

theorem dispatch_run (B : ℕ) (cases : List Com) (i j K : ℕ) (hj : j<cases.length)
    (hB : i+cases.length+2<B) {σ τ : Env} (hphase : σ.vars "machine.phase"=i+j)
    (rr : Run B cases[j] σ τ K) : Run B (dispatch cases i) σ τ (K+4*(j+1)) := by
  induction cases generalizing i j K with
  | nil => simp at hj
  | cons c cs ih =>
    have hphaseB : i+j<B := by simp only [List.length_cons] at hj hB; omega
    have hc : (Cond.eq (.var "machine.phase") (.lit i)).evalB B σ=some (decide (i+j=i)) := by
      have hh : (Cond.eq (.var "machine.phase") (.lit i)).evalB B σ=some ((i+j)==i) := evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨hphase.symm,hphase ▸ hphaseB⟩)
        (evalB_lit (show i<B by simp only [List.length_cons] at hB; omega))
      have he : ((i+j)==i)=decide (i+j=i) := by
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq,decide_eq_true_eq]
      exact hh.trans (congrArg some he)
    cases j with
    | zero =>
      have rb : Run B c σ τ K := by simpa only [List.getElem_cons_zero] using rr
      exact (Run.ite_true (d:=dispatch cs (i+1)) (by simpa using hc) rb).mono
        (by simp [Cond.size,Expr.size] <;> omega)
    | succ j =>
      have hcs : j<cs.length := by simp only [List.length_cons] at hj; omega
      have rb := ih (i+1) j K hcs (by simp only [List.length_cons] at hB; omega)
        (by simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1] using hphase)
        (by simpa only [List.getElem_cons_succ] using rr)
      exact (Run.ite_false (c:=c) (by simpa using hc) rb).mono
        (by simp [Cond.size,Expr.size,Nat.succ_eq_add_one]; omega)

/-- Translate the compositional trace of all child calls and returns
into execution of one fixed native dispatcher loop, with explicit
constant overhead per phase. -/
theorem driver_run {B steps total : ℕ} {cases : List Com} {σ τ : Env}
    (tr : Trace B cases steps total σ τ) (hB : cases.length+2<B) :
    Run B (driver cases) σ τ (total+(4*cases.length+4)*steps+4) := by
  induction tr with
  | stop h =>
    rename_i σ0
    have hc : (Cond.eq (.var "machine.running") (.lit 1)).evalB B σ0=some false := by
      have hh := evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨h.symm,h ▸ (by omega : 0<B)⟩) (evalB_lit (show 1<B by omega))
      simpa using hh
    exact (Run.while_false hc).mono (by simp [Cond.size,Expr.size])
  | step h j hj rr rest ih =>
    rename_i σ0 μ0 τ0 steps0 total0 cost0
    have hc : (Cond.eq (.var "machine.running") (.lit 1)).evalB B σ0=some true := by
      have hh := evalB_condEq
        (by rw [evalB_var_iff]; exact ⟨h.symm,h ▸ (by omega : 1<B)⟩) (evalB_lit (show 1<B by omega))
      simpa using hh
    have rb := dispatch_run B cases 0 j.val _ j.isLt (by simpa only [Nat.zero_add] using hB)
      (by simpa only [Nat.zero_add] using hj) rr
    have hcost : 4*(j.val+1)≤4*cases.length := Nat.mul_le_mul_left _ j.isLt
    exact (while_true_run hc (rb.mono (Nat.add_le_add_left hcost _)) ih).mono
      (by simp only [Cond.size,Expr.size]; nlinarith only [])

end Lax263307Proofs.NativeMachineTrace
