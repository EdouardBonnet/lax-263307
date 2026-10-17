import Lax263307.IndependentSetEncoding
import Lax263307Proofs.NativeExhaustive
import Lax263307Proofs.NativeTargetDriver

namespace Lax263307Proofs.NativeAttemptReply

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeMasks

def someCommand (ret : ℕ) : Com := .seq NativeMasks.command
  (.seq (.assign "recursion.return.tag" (.lit 1))
    (.seq (.assign "recursion.return.mask" (.var "mask.value")) (.assign "machine.phase" (.lit ret))))

def noneCommand (ret : ℕ) : Com := .seq (.assign "recursion.return.tag" (.lit 0))
  (.seq (.assign "recursion.return.mask" (.lit 0)) (.assign "machine.phase" (.lit ret)))

def command (ret : ℕ) : Com := .ite (.eq (.var "target.found") (.lit 1)) (someCommand ret) (noneCommand ret)

theorem none_spec (B n ret : ℕ) (hB : n+ret+5<B) :
    Spec B (fun σ => σ.vars "graph.n"=n) (noneCommand ret)
      (fun _ τ => τ.vars "graph.n"=n ∧ NativeTargetDriver.Reply (none : Option (Finset (Fin n))) τ ∧
        τ.vars "machine.phase"=ret) 6 := by
  intro σ hs
  run_vcg
  all_goals simp_all [NativeTargetDriver.Reply,Env.setVar]
  all_goals omega

theorem some_spec (B n ret : ℕ) (I : Finset (Fin n)) (hB : n+ret+5<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ Lax455465Proofs.RamVirtualState.Prefix
      (IndependentSetEncoding.encodeOutput I) "subset.bits" σ) (someCommand ret)
      (fun _ τ => τ.vars "graph.n"=n ∧ NativeTargetDriver.Reply (some I) τ ∧
        τ.vars "machine.phase"=ret) (15*n+14) := by
  rintro σ ⟨hn,hbits⟩
  obtain ⟨ν,r1,p1⟩ := NativeMasks.command_spec B I (by omega) hm σ ⟨hn,hbits⟩
  let μ := ν.setVar "recursion.return.tag" 1
  have r2 : Run B (.assign "recursion.return.tag" (.lit 1)) ν μ 2 := Run.assign (evalB_lit (show 1<B by omega))
  have hmμ := (r2.frame_var "mask.value" (by decide)).trans p1
  let ρ := μ.setVar "recursion.return.mask" (mask I)
  have r3 : Run B (.assign "recursion.return.mask" (.var "mask.value")) μ ρ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hmμ.symm,hmμ ▸ (mask_bound I).trans hm⟩)
  let τ := ρ.setVar "machine.phase" ret
  have r4 : Run B (.assign "machine.phase" (.lit ret)) ρ τ 2 := Run.assign (evalB_lit (show ret<B by omega))
  have rr := r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr.mono (by omega),(rr.frame_var "graph.n" (by simp [Com.wvars,NativeMasks.command,NativeMasks.step])).trans hn,
    ⟨((r3.seq r4).frame_var "recursion.return.tag" (by simp [Com.wvars])).trans (by rfl),
      (r4.frame_var "recursion.return.mask" (by simp [Com.wvars])).trans (by rfl)⟩,by rfl⟩

/-- Turn exhaustive-search bits into the same return protocol used
by recursive calls, with an exact selected-set mask. -/
theorem command_spec (B n ret : ℕ) (answer : Option (Finset (Fin n)))
    (hB : n+ret+5<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ NativeExhaustive.Result answer σ) (command ret)
      (fun _ τ => τ.vars "graph.n"=n ∧ NativeTargetDriver.Reply answer τ ∧ τ.vars "machine.phase"=ret)
      (15*n+18) := by
  rintro σ ⟨hn,hr⟩
  cases answer with
  | none =>
    have hc : (Cond.eq (.var "target.found") (.lit 1)).evalB B σ=some false := by
      have hh := evalB_condEq (by rw [evalB_var_iff]; exact ⟨hr.symm,hr ▸ (by omega : 0<B)⟩)
        (evalB_lit (show 1<B by omega))
      simpa using hh
    obtain ⟨τ,rr,p⟩ := none_spec B n ret hB σ hn
    exact ⟨τ,(Run.ite_false (c:=someCommand ret) hc rr).mono (by simp [Cond.size,Expr.size] <;> omega),p⟩
  | some I =>
    have hc : (Cond.eq (.var "target.found") (.lit 1)).evalB B σ=some true := by
      have hh := evalB_condEq (by rw [evalB_var_iff]; exact ⟨hr.1.symm,hr.1 ▸ (by omega : 1<B)⟩)
        (evalB_lit (show 1<B by omega))
      simpa using hh
    obtain ⟨τ,rr,p⟩ := some_spec B n ret I hB hm σ ⟨hn,hr.2⟩
    exact ⟨τ,(Run.ite_true (d:=noneCommand ret) hc rr).mono (by simp [Cond.size,Expr.size] <;> omega),p⟩

end Lax263307Proofs.NativeAttemptReply
