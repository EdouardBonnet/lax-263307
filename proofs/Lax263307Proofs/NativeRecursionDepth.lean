import Lax263307Proofs.NativeTabulate
import Lax263307Proofs.RecursionDepth

namespace Lax263307Proofs.NativeRecursionDepth

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.RecursionDepth

def step : Com := .seq (.assign "depth.value" (.div (.mul (.lit 2) (.var "depth.value")) (.lit 3)))
  (.assign "depth.count" (.add (.var "depth.count") (.lit 1)))
def loop : Com := .while (.lt (.lit 1) (.var "depth.value")) step
def command : Com := .seq (.assign "depth.value" (.var "graph.n"))
  (.seq (.assign "depth.count" (.lit 0)) loop)

def Invariant (n : ℕ) (σ : Env) : Prop :=
  σ.vars "depth.value"≤n ∧ σ.vars "depth.count"+depth (σ.vars "depth.value")=depth n

/-- Compute the actual balanced-recursion depth by integer reductions,
with one fixed loop and an explicit logarithmic number of steps. -/
theorem command_spec (B n : ℕ) (hB : 2*n+depth n+10<B) :
    Spec B (fun σ => σ.vars "graph.n"=n) command
      (fun _ τ => τ.vars "graph.n"=n ∧ τ.vars "depth.count"=depth n) (14*depth n+8) := by
  have hlo : Spec B (fun σ => σ.vars "depth.value"=n ∧ σ.vars "depth.count"=0) loop
      (fun _ τ => Invariant n τ ∧ (Cond.lt (.lit 1) (.var "depth.value")).evalB B τ=some false)
      (14*depth n+4) := by
    apply Spec.while_count (Invariant n) (fun σ => depth (σ.vars "depth.value")) 10
    · intro σ hs
      exact ⟨_,evalB_condLt (evalB_lit (show 1<B by omega)) (evalB_var (hs.1.trans_lt (by omega)))⟩
    · rintro σ ⟨hs,hcond⟩
      have hvB : σ.vars "depth.value"<B := hs.1.trans_lt (by omega)
      have hval : 1<σ.vars "depth.value" := by
        rw [evalB_condLt (evalB_lit (show 1<B by omega)) (evalB_var hvB)] at hcond
        simpa using hcond
      have hd : depth (σ.vars "depth.value")=1+depth (2*σ.vars "depth.value"/3) := by
        rw [depth,if_neg (by omega)]
      have hcB : σ.vars "depth.count"+1<B := by have hh:=hs.2; omega
      have hmB : 2*σ.vars "depth.value"<B := by have hh:=hs.1; omega
      have hnext : 2*σ.vars "depth.value"/3≤n := by have hh:=hs.1; omega
      run_vcg
      all_goals simp_all [Invariant,Env.setVar]
      all_goals omega
    · rintro σ ⟨hv,hc⟩
      simp [Invariant,hv,hc]
    · rintro σ ⟨hv,_⟩
      simp [hv]
  have hfinish : Spec B (fun σ => σ.vars "depth.value"=n ∧ σ.vars "depth.count"=0) loop
      (fun _ τ => τ.vars "depth.count"=depth n) (14*depth n+4) := hlo.post (by
    rintro σ τ _ ⟨hs,hcond⟩
    have hvB : τ.vars "depth.value"<B := hs.1.trans_lt (by omega)
    have hsmall : τ.vars "depth.value"≤1 := by
      rw [evalB_condLt (evalB_lit (show 1<B by omega)) (evalB_var hvB)] at hcond
      have hh : ¬1<τ.vars "depth.value" := by simpa using hcond
      omega
    have hz : depth (τ.vars "depth.value")=0 := by rw [depth,if_pos hsmall]
    simpa only [hz,Nat.add_zero] using hs.2)
  intro σ hs
  let ν := σ.setVar "depth.value" n
  have r1 : Run B (.assign "depth.value" (.var "graph.n")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ (by omega)⟩)
  let μ := ν.setVar "depth.count" 0
  have r2 : Run B (.assign "depth.count" (.lit 0)) ν μ 2 := Run.assign (evalB_lit (show 0<B by omega))
  obtain ⟨τ,r3,p3⟩ := hfinish μ ⟨by simp [μ,ν],by rfl⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),
    ((r1.seq (r2.seq r3)).frame_var "graph.n" (by decide)).trans hs,p3⟩

end Lax263307Proofs.NativeRecursionDepth
