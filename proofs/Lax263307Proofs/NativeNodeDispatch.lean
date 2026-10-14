import Lax263307Proofs.NativeNodeParameters
import Lax263307Proofs.NativeAttemptReply
import Lax263307.RecursiveAlgorithm

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodeDispatch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 AlgorithmParameters

inductive Route | exhaustive | reject | search
  deriving DecidableEq

def route (n k threshold fuel : ℕ) : Route :=
  if k≤threshold ∨ n≤1 then .exhaustive else if n<k ∨ fuel=0 then .reject else .search

def Output (small large ret : ℕ) : Route → Env → Prop
  | .exhaustive, σ => σ.vars "machine.phase"=small
  | .reject, σ => σ.vars "machine.phase"=ret ∧ σ.vars "recursion.return.tag"=0
  | .search, σ => σ.vars "machine.phase"=large

def select (small large ret : ℕ) : Com :=
  .ite (.lt (.var "node.k") (.add (.var "node.cutoff") (.lit 1)))
    (.assign "machine.phase" (.lit small))
    (.ite (.lt (.var "graph.n") (.var "node.k")) (NativeAttemptReply.noneCommand ret)
      (.ite (.eq (.var "recursion.fuel") (.lit 0)) (NativeAttemptReply.noneCommand ret)
        (.assign "machine.phase" (.lit large))))

private theorem value {B x : ℕ} {s : String} {σ : Env} (h : σ.vars s=x) (hx : x<B) :
    (Expr.var s).evalB B σ=some x := by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem select_spec (B n k threshold fuel small large ret : ℕ) (hn : 1<n)
    (hB : n+k+threshold+fuel+small+large+ret+10<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "node.k"=k ∧ σ.vars "node.cutoff"=threshold ∧
      σ.vars "recursion.fuel"=fuel) (select small large ret)
      (fun _ τ => Output small large ret (route n k threshold fuel) τ) 20 := by
  rintro σ ⟨hnσ,hk,ht,hf⟩
  have hsmall : (Cond.lt (.var "node.k") (.add (.var "node.cutoff") (.lit 1))).evalB B σ=
      some (decide (k≤threshold)) := by
    have hh := evalB_condLt (value hk (by omega))
      (evalB_bin (op:=.add) (value ht (by omega)) (evalB_lit (show 1<B by omega))
        (by change threshold+1<B; omega))
    simpa only [Bop.apply_add,Nat.lt_succ_iff] using hh
  have hlarge : (Cond.lt (.var "graph.n") (.var "node.k")).evalB B σ=some (decide (n<k)) :=
    evalB_condLt (value hnσ (by omega)) (value hk (by omega))
  have hzero : (Cond.eq (.var "recursion.fuel") (.lit 0)).evalB B σ=some (decide (fuel=0)) := by
    simpa only [Bool.beq_eq_decide_eq] using evalB_condEq (value hf (by omega)) (evalB_lit (show 0<B by omega))
  by_cases hs : k≤threshold
  · let τ := σ.setVar "machine.phase" small
    have rr : Run B (.assign "machine.phase" (.lit small)) σ τ 2 := Run.assign (evalB_lit (show small<B by omega))
    refine ⟨τ,(Run.ite_true (d:=.ite (.lt (.var "graph.n") (.var "node.k")) (NativeAttemptReply.noneCommand ret)
      (.ite (.eq (.var "recursion.fuel") (.lit 0)) (NativeAttemptReply.noneCommand ret)
        (.assign "machine.phase" (.lit large)))) (by simpa only [hs,decide_true] using hsmall) rr).mono
      (by simp [Cond.size,Expr.size]),?_⟩
    simp [Output,route,hs,τ]
  · have hnot : ¬(k≤threshold ∨ n≤1) := by omega
    by_cases hk' : n<k
    · obtain ⟨τ,rr,p⟩ := NativeAttemptReply.none_spec B n ret (by omega) σ hnσ
      have r2 := Run.ite_true (d:=.ite (.eq (.var "recursion.fuel") (.lit 0))
        (NativeAttemptReply.noneCommand ret) (.assign "machine.phase" (.lit large)))
        (by simpa only [hk',decide_true] using hlarge) rr
      refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
        (by simpa only [hs,decide_false] using hsmall) r2).mono (by simp [Cond.size,Expr.size]),?_⟩
      simpa only [route,if_neg hnot,hk',true_or,if_true,Output] using (show τ.vars "machine.phase"=ret ∧ τ.vars "recursion.return.tag"=0 from ⟨p.2.2,p.2.1⟩)
    · by_cases hz : fuel=0
      · obtain ⟨τ,rr,p⟩ := NativeAttemptReply.none_spec B n ret (by omega) σ hnσ
        have r3 := Run.ite_true (d:=.assign "machine.phase" (.lit large))
          (by simpa only [hz,decide_true] using hzero) rr
        have r2 := Run.ite_false (c:=NativeAttemptReply.noneCommand ret)
          (by simpa only [hk',decide_false] using hlarge) r3
        refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
          (by simpa only [hs,decide_false] using hsmall) r2).mono (by simp [Cond.size,Expr.size]),?_⟩
        simpa only [route,if_neg hnot,hz,or_true,if_true,Output] using (show τ.vars "machine.phase"=ret ∧ τ.vars "recursion.return.tag"=0 from ⟨p.2.2,p.2.1⟩)
      · let τ := σ.setVar "machine.phase" large
        have rr : Run B (.assign "machine.phase" (.lit large)) σ τ 2 := Run.assign (evalB_lit (show large<B by omega))
        have r3 := Run.ite_false (c:=NativeAttemptReply.noneCommand ret) (by simpa only [hz,decide_false] using hzero) rr
        have r2 := Run.ite_false (c:=NativeAttemptReply.noneCommand ret) (by simpa only [hk',decide_false] using hlarge) r3
        refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
          (by simpa only [hs,decide_false] using hsmall) r2).mono (by simp [Cond.size,Expr.size]),?_⟩
        simp [route,hnot,hk',hz,Output,τ]

def command (a K b small large ret : ℕ) : Com :=
  .ite (.lt (.var "graph.n") (.lit 2)) (.assign "machine.phase" (.lit small))
    (.seq (NativeNodeParameters.command a K b) (select small large ret))

def Input (n D k fuel : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "node.D"=D ∧ σ.vars "node.k"=k ∧ σ.vars "recursion.fuel"=fuel

/-- A fixed node-entry handler makes exactly the case distinction of
RecursiveAlgorithm.attempt, computing its cutoff from the current graph.
Graphs of order zero or one bypass logarithm-dependent initialization. -/
theorem command_spec (B a K b n D k fuel small large ret : ℕ)
    (hB : NativeNodeParameters.guard a K b n D+n+k+cutoff a K b n D+fuel+small+large+ret+10<B) :
    Spec B (Input n D k fuel) (command a K b small large ret)
      (fun _ τ => Input n D k fuel τ ∧ Output small large ret (route n k (cutoff a K b n D) fuel) τ ∧
        (route n k (cutoff a K b n D) fuel=.search → NativeNodeParameters.Data a K b n D τ))
      (12*n.size+12*(2*n).size+12*(4*a+2)+88) := by
  rintro σ ⟨hn,hD,hk,hf⟩
  have htest := evalB_condLt (value hn (show n<B by omega)) (evalB_lit (show 2<B by omega))
  by_cases hs : n<2
  · let τ := σ.setVar "machine.phase" small
    have rr : Run B (.assign "machine.phase" (.lit small)) σ τ 2 := Run.assign (evalB_lit (show small<B by omega))
    refine ⟨τ,(Run.ite_true (d:=.seq (NativeNodeParameters.command a K b) (select small large ret))
      (by simpa only [hs,decide_true] using htest) rr).mono (by simp [Cond.size,Expr.size] <;> omega),?_,?_,?_⟩
    · simpa [Input,τ] using (show Input n D k fuel σ from ⟨hn,hD,hk,hf⟩)
    · have hsmall : n≤1 := by omega
      simp [route,hsmall,Output,τ]
    · have hsmall : n≤1 := by omega
      simp [route,hsmall]
  · obtain ⟨ν,r1,p1⟩ := NativeNodeParameters.command_spec B a K b n D (by omega) (by omega) σ ⟨hn,hD⟩
    have hk1 : ν.vars "node.k"=k := (r1.frame_var _ (by
      change "node.k"∉(NativeNodeParameters.command 0 0 0).wvars
      decide)).trans hk
    have hf1 : ν.vars "recursion.fuel"=fuel := (r1.frame_var _ (by
      change "recursion.fuel"∉(NativeNodeParameters.command 0 0 0).wvars
      decide)).trans hf
    obtain ⟨τ,r2,p2⟩ := select_spec B n k (cutoff a K b n D) fuel small large ret (by omega) (by omega) ν
      ⟨p1.1.1,hk1,p1.2.2.2.2.2.1,hf1⟩
    have hn2 := (r2.frame_var "graph.n" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans p1.1.1
    have hD2 := (r2.frame_var "node.D" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans p1.1.2.1
    have hk2 := (r2.frame_var "node.k" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans hk1
    have hf2 := (r2.frame_var "recursion.fuel" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])).trans hf1
    refine ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit small))
      (by simpa only [hs,decide_false] using htest) (r1.seq r2)).mono (by simp [Cond.size,Expr.size] <;> omega),
      ⟨hn2,hD2,hk2,hf2⟩,p2,?_⟩
    intro _
    simpa only [NativeNodeParameters.Data,NativeNodeParameters.Context,
      r2.frame_var "graph.n" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.D" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.log" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.logarithm" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.load" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.threshold" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.sparsity" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "moment.r" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.cutoff" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars]),
      r2.frame_var "node.floorDen" (by simp [select,NativeAttemptReply.noneCommand,Com.wvars])] using p1

end Lax263307Proofs.NativeNodeDispatch
