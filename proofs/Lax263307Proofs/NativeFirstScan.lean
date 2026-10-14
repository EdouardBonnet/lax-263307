import Lax263307Proofs.NativeWordLookup

set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeFirstScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def update : Com := .seq
  (.ite (.eq (.var "scan.accepted") (.lit 1))
    (.ite (.eq (.var "scan.result") (.var "scan.count"))
      (.assign "scan.result" (.var "scan.i")) .skip) .skip)
  (.assign "scan.i" (.add (.var "scan.i") (.lit 1)))

def command (read : Com) : Com := .seq (.assign "scan.result" (.var "scan.count"))
  (.seq (.assign "scan.i" (.lit 0)) (.while (.lt (.var "scan.i") (.var "scan.count")) (.seq read update)))

def Invariant (N f : ℕ) (P : Env → Prop) (σ : Env) : Prop :=
  P σ ∧ σ.vars "scan.i"≤N ∧ σ.vars "scan.result"=if f<σ.vars "scan.i" then f else N

theorem update_spec (B N f i : ℕ) (b : Bool) (hB : N+3<B) (hf : f≤N) (hi : i<N)
    (hbefore : i<f → b=false) (hat : i=f → b=true) :
    Spec B (fun σ => σ.vars "scan.count"=N ∧ σ.vars "scan.i"=i ∧
      σ.vars "scan.result"=(if f < i then f else N) ∧ σ.vars "scan.accepted"=(if b then 1 else 0)) update
      (fun _ τ => τ.vars "scan.i"=i+1 ∧ τ.vars "scan.result"=if f < i+1 then f else N) 14 := by
  cases b <;> run_vcg
  all_goals simp_all
  all_goals first | omega | (split_ifs at * <;> omega)

/-- Execute a supplied bounded predicate in catalog order and retain
the first accepting index. The length itself is the no-match sentinel. -/
theorem command_spec (B N f K : ℕ) (P : Env → Prop) (read : Com) (accepted : Fin N → Bool)
    (hB : N+3<B) (hf : f≤N)
    (hbefore : ∀ i : Fin N,i.val<f → accepted i=false)
    (hat : ∀ h : f<N,accepted ⟨f,h⟩=true)
    (hcount : ∀ σ,P σ → σ.vars "scan.count"=N)
    (hinit : ∀ σ k,P σ → P (σ.setVar "scan.i" k))
    (hresult : ∀ σ k,P σ → P (σ.setVar "scan.result" k))
    (hwrite : ∀ σ τ,Run B update σ τ 14 → P σ → P τ)
    (hri : "scan.i"∉read.wvars) (hrr : "scan.result"∉read.wvars)
    (hread : ∀ i : Fin N,Spec B (fun σ => P σ ∧ σ.vars "scan.i"=i.val) read
      (fun _ τ => P τ ∧ τ.vars "scan.accepted"=if accepted i then 1 else 0) K) :
    Spec B P (command read) (fun _ τ => P τ ∧ τ.vars "scan.result"=f) ((K+18)*N+8) := by
  have hbody : Spec B (fun σ => Invariant N f P σ ∧ σ.vars "scan.i"<N) (.seq read update)
      (fun σ τ => Invariant N f P τ ∧ τ.vars "scan.i"=σ.vars "scan.i"+1) (K+14) := by
    rintro σ ⟨⟨hP,hle,hres⟩,hlt⟩
    let i : Fin N := ⟨σ.vars "scan.i",hlt⟩
    obtain ⟨ν,r1,p1⟩ := hread i σ ⟨hP,rfl⟩
    have hiν : ν.vars "scan.i"=i.val := r1.frame_var "scan.i" hri
    obtain ⟨τ,r2,p2⟩ := update_spec B N f i.val (accepted i) hB hf i.isLt (hbefore i)
      (by intro he; have hh := hat (by omega); simpa only [←he] using hh) ν
      ⟨hcount ν p1.1,hiν,(r1.frame_var "scan.result" hrr).trans hres,p1.2⟩
    exact ⟨τ,r1.seq r2,⟨hwrite ν τ r2 p1.1,by rw [p2.1]; exact i.isLt,
      by simpa only [p2.1] using p2.2⟩,p2.1⟩
  have hloop := Spec.forRangeZero "scan.i" "scan.count" (Invariant N f P) N (K+14) (by omega)
    (fun _ h => h.2.1) (fun σ h => hcount σ h.1) hbody
  intro σ hP
  have hc := hcount σ hP
  let ν := σ.setVar "scan.result" N
  have r1 : Run B (.assign "scan.result" (.var "scan.count")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hc.symm,hc ▸ (by omega : N<B)⟩)
  have hinit' : Invariant N f P (ν.setVar "scan.i" 0) := by
    exact ⟨hinit ν 0 (hresult σ N hP),by simp,by simp [ν]⟩
  obtain ⟨τ,r2,p2⟩ := hloop ν hinit'
  have he : (if f<N then f else N)=f := by split_ifs <;> omega
  exact ⟨τ,(r1.seq r2).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),p2.1.1,
    by simpa only [p2.2,he] using p2.1.2.2⟩

end Lax263307Proofs.NativeFirstScan
