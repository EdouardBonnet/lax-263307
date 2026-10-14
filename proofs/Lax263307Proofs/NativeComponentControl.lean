import Lax263307Proofs.NativeOracleCut
import Lax263307Proofs.NativeChildReturn
import Lax263307Proofs.NativeSetMasks
import Lax263307Proofs.NativeTargetDriver

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeComponentControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks ComputedSeparators

def start (next : ℕ) : Com := .seq (.assign "component.count" (.add (.var "separator.count") (.lit 1)))
  (.seq (.assign "component.i" (.lit 0)) (.seq (.assign "component.union" (.lit 0))
    (.assign "machine.phase" (.lit next))))

theorem start_spec (B q next : ℕ) (hB : q+next+3<B) :
    Spec B (fun σ => σ.vars "separator.count"=q) (start next)
      (fun _ τ => τ.vars "component.count"=q+1 ∧ τ.vars "component.i"=0 ∧
        τ.vars "component.union"=0 ∧ τ.vars "machine.phase"=next) 10 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

def advance (next : ℕ) : Com := .seq (.assign "component.i" (.add (.var "component.i") (.lit 1)))
  (.assign "machine.phase" (.lit next))

theorem advance_spec (B i next : ℕ) (hB : i+next+3<B) :
    Spec B (fun σ => σ.vars "component.i"=i) (advance next)
      (fun _ τ => τ.vars "component.i"=i+1 ∧ τ.vars "machine.phase"=next) 6 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

def append (next : ℕ) : Com := .seq
  (.assign "component.union" (.or (.var "component.union") (.var "lift.mask"))) (advance next)

theorem append_spec {n : ℕ} (B i next : ℕ) (S I : Finset (Fin n))
    (hB : i+next+3<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "component.i"=i ∧ σ.vars "component.union"=mask S ∧ σ.vars "lift.mask"=mask I)
      (append next) (fun _ τ => τ.vars "component.i"=i+1 ∧ τ.vars "component.union"=mask (S∪I) ∧
        τ.vars "machine.phase"=next) 10 := by
  rintro σ ⟨hi,hs,hI⟩
  let ν := σ.setVar "component.union" (mask (S∪I))
  have r1 : Run B (.assign "component.union" (.or (.var "component.union") (.var "lift.mask"))) σ ν 4 := by
    apply Run.assign
    rw [NativeSetMasks.union]
    exact evalB_bin (op:=.or)
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ (mask_bound S).trans hm⟩)
      (by rw [evalB_var_iff]; exact ⟨hI.symm,hI ▸ (mask_bound I).trans hm⟩)
      (by change Nat.lor (mask S) (mask I)<B; rw [←NativeSetMasks.union]; exact (mask_bound _).trans hm)
  obtain ⟨τ,r2,p2⟩ := advance_spec B i next hB ν ((r1.frame_var _ (by decide)).trans hi)
  exact ⟨τ,r1.seq r2,p2.1,(r2.frame_var _ (by simp [advance,Com.wvars])).trans (by simp [ν]),p2.2⟩

def childReply (more update : ℕ) : Com := .ite (.eq (.var "recursion.return.tag") (.lit 1))
  (.seq NativeChildReturn.liftCommand (append more)) (NativeOracleCut.failedChild update)

/-- After restoring the parent frame, a successful child is lifted to
parent labels, accumulated, and followed by the next component. -/
theorem child_some_spec {n : ℕ} (B i more update : ℕ) (C S : Finset (Fin n))
    (I : Finset (Fin C.card)) (hB : n+i+more+5<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "recursion.return.tag"=1 ∧ σ.vars "graph.n"=n ∧
      σ.vars "restrict.count"=C.card ∧ σ.vars "recursion.return.mask"=mask I ∧
      Prefix (NativeRestrictionOrder.words C) "restrict.vertices" σ ∧ C.card≤(σ.arrs "subset.bits").length ∧
      σ.vars "component.i"=i ∧ σ.vars "component.union"=mask S)
      (childReply more update) (fun _ τ => τ.vars "graph.n"=n ∧ τ.vars "component.i"=i+1 ∧
        τ.vars "component.union"=mask (S∪I.image (label C)) ∧ τ.vars "machine.phase"=more)
      (45*C.card+38) := by
  rintro σ ⟨htag,hn,hc,hmask,hlabels,hroom,hi,hs⟩
  obtain ⟨ν,r1,p1⟩ := NativeChildReturn.lift_spec B n C I (by omega) hm σ ⟨hn,hc,hmask,hlabels,hroom⟩
  obtain ⟨τ,r2,p2⟩ := append_spec B i more S (I.image (label C)) (by omega) hm ν
    ⟨(r1.frame_var _ (by decide)).trans hi,(r1.frame_var _ (by decide)).trans hs,p1.2.1⟩
  have hcond : (Cond.eq (.var "recursion.return.tag") (.lit 1)).evalB B σ=some true := by
    have hh := evalB_condEq
      (by rw [evalB_var_iff]; exact ⟨htag.symm,htag ▸ (by omega : 1<B)⟩) (evalB_lit (show 1<B by omega))
    simpa using hh
  exact ⟨τ,(Run.ite_true (d:=NativeOracleCut.failedChild update) hcond (r1.seq r2)).mono
    (by simp [Cond.size,Expr.size]; omega),
    (r2.frame_var _ (by simp [append,advance,Com.wvars])).trans p1.1,p2⟩

/-- A failed child stops component collection at that component and
constructs its target-minus-one cut. -/
theorem child_none_spec {n : ℕ} (B r more update : ℕ) (A C : Finset (Fin n)) (t : ℕ)
    (hB : n+t+3*NativeCatalogMetadata.N n r+update+10<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "recursion.return.tag"=0 ∧ NativeComponentNormal.Data r A C t σ ∧
      NativeArrayBounds.Bounded B σ ∧ 3*NativeCatalogMetadata.N n r≤(σ.arrs "lp.input").length ∧
      3*NativeCatalogMetadata.N n r≤(σ.arrs "round.normal").length)
      (childReply more update) (fun _ τ => Prefix (NativeRoundedQuery.normal
        (RationalCutBuffer.integerNormal (RoundedOracleSearch.rationalNormal
          (NativeComponentNormal.normal (r:=r) A C (t-1))))) "round.normal" τ ∧ τ.vars "machine.phase"=update)
      ((28*n+104)*NativeCatalogMetadata.N n r+30) := by
  rintro σ ⟨htag,hd⟩
  obtain ⟨τ,rr,p⟩ := NativeOracleCut.failed_child_spec B r update A C t hB hm σ hd
  have hcond : (Cond.eq (.var "recursion.return.tag") (.lit 1)).evalB B σ=some false := by
    have hh := evalB_condEq
      (by rw [evalB_var_iff]; exact ⟨htag.symm,htag ▸ (by omega : 0<B)⟩) (evalB_lit (show 1<B by omega))
    simpa using hh
  exact ⟨τ,(Run.ite_false (c:=.seq NativeChildReturn.liftCommand (append more)) hcond rr).mono
    (by simp [Cond.size,Expr.size]; omega),p⟩

def finish (ret : ℕ) : Com := .seq (.assign "recursion.return.tag" (.lit 1))
  (.seq (.assign "recursion.return.mask" (.var "component.union")) (.assign "machine.phase" (.lit ret)))

theorem finish_spec {n : ℕ} (B ret : ℕ) (S : Finset (Fin n)) (hB : ret+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "component.union"=mask S) (finish ret)
      (fun _ τ => NativeTargetDriver.Reply (some S) τ ∧ τ.vars "machine.phase"=ret) 6 := by
  have hmask : mask S<B := (mask_bound S).trans hm
  intro σ hs
  run_vcg
  all_goals simp_all [NativeTargetDriver.Reply,Env.setVar]
  all_goals omega

end Lax263307Proofs.NativeComponentControl
