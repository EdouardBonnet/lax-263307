import Lax263307Proofs.NativeRoundedUpdate
import Lax263307Proofs.NativeAttemptReply

namespace Lax263307Proofs.NativeRoundedControl

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch Matrix

def finish (projection ret : ℕ) : Com := .seq
  (.assign "round.i" (.add (.var "round.i") (.lit 1)))
  (.ite (.lt (.var "round.i") (.var "round.limit")) (.assign "machine.phase" (.lit projection))
    (NativeAttemptReply.noneCommand ret))

def Output (m k limit projection ret : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=m ∧ σ.vars "round.i"=k+1 ∧
    if k+1<limit then σ.vars "machine.phase"=projection
    else NativeTargetDriver.Reply (none : Option (Finset (Fin m))) σ ∧ σ.vars "machine.phase"=ret

theorem finish_spec (B m k limit projection ret : ℕ) (hB : m+k+limit+projection+ret+10<B) :
    Spec B (fun σ => σ.vars "graph.n"=m ∧ σ.vars "round.i"=k ∧ σ.vars "round.limit"=limit)
      (finish projection ret) (fun _ τ => Output m k limit projection ret τ) 14 := by
  rintro σ ⟨hm,hk,hl⟩
  let ν := σ.setVar "round.i" (k+1)
  have r1 : Run B (.assign "round.i" (.add (.var "round.i") (.lit 1))) σ ν 4 := Run.assign
    (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hk.symm,hk ▸ (by omega)⟩)
      (evalB_lit (show 1<B by omega)) (by change k+1<B; omega))
  have hiν : ν.vars "round.i"=k+1 := by simp [ν]
  have hlν := (r1.frame_var "round.limit" (by decide)).trans hl
  have hnν := (r1.frame_var "graph.n" (by decide)).trans hm
  have hc : (Cond.lt (.var "round.i") (.var "round.limit")).evalB B ν=some (decide (k+1<limit)) :=
    evalB_condLt
      (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by omega)⟩)
      (by rw [evalB_var_iff]; exact ⟨hlν.symm,hlν ▸ (by omega)⟩)
  by_cases hs : k+1<limit
  · let τ := ν.setVar "machine.phase" projection
    have rr : Run B (.assign "machine.phase" (.lit projection)) ν τ 2 := Run.assign (evalB_lit (show projection<B by omega))
    have r2 := Run.ite_true (d:=NativeAttemptReply.noneCommand ret) (by simpa only [hs,decide_true] using hc) rr
    refine ⟨τ,(r1.seq r2).mono (by simp [Cond.size,Expr.size]),?_,?_,?_⟩
    · exact (rr.frame_var _ (by simp [Com.wvars])).trans hnν
    · exact (rr.frame_var _ (by simp [Com.wvars])).trans hiν
    · simp [hs,τ]
  · obtain ⟨τ,rr,p⟩ := NativeAttemptReply.none_spec B m ret (by omega) ν hnν
    have r2 := Run.ite_false (c:=.assign "machine.phase" (.lit projection)) (by simpa only [hs,decide_false] using hc) rr
    refine ⟨τ,(r1.seq r2).mono (by simp [Cond.size,Expr.size]),p.1,?_,?_⟩
    · exact (rr.frame_var _ (by simp [NativeAttemptReply.noneCommand,Com.wvars])).trans hiν
    · simpa only [hs,if_false] using p.2

def command (p : Lax808846.Ram.Program) (projection ret : ℕ) : Com :=
  .seq (.assign "vm.width" (.var "algorithm.roundWidth"))
    (.seq (NativeRoundedUpdate.command p) (finish projection ret))

theorem update_variable (p : Lax808846.Ram.Program) (s : String)
    (hq : s∉NativeRoundedQuery.command.wvars) (hpre : s∉NativeRawOracle.prepare.wvars)
    (hvm : s∉NativeOracleScalars.reserved) (hs : s∉NativeRoundedState.command.wvars) :
    s∉(NativeRoundedUpdate.command p).wvars := by
  simpa only [NativeRoundedUpdate.command,Com.wvars,List.mem_append,not_or] using
    And.intro hq (And.intro (NativeRawFrame.command_variable p s hpre hvm) hs)

/-- The complete update phase resets the virtual width after LP/flow calls,
performs the checked update, advances the actual iteration counter, and
either starts the next projection or returns failure at the search limit. -/
theorem exists_program : ∃ (p : Lax808846.Ram.Program) (c : ℕ),0<c ∧
    ∀ (n m k h limit projection ret : ℕ),2≤n → 1≤h →
    ∀ (state : State n) (a : Fin n → ℤ),
    (∀ i j,Lax263307.NativeRoundedStep.height (state.1 i j) h) →
    (∀ i,Lax263307.NativeRoundedStep.height (rationalNormal a i) h) →
    (∀ i,Lax263307.NativeRoundedStep.height (state.2 i) h) →
    0<rationalNormal a ⬝ᵥ (state.1 *ᵥ rationalNormal a) →
    ∀ (B v : ℕ),c*(n+h+k+1)^12≤v →
    let T := c*(n+h+k+1)^12
    let xs := Lax263307.NativeRoundedStep.encodeInput k state a
    2*(2^v)^2+3<B → T+1<B → RamVirtualConstants.allowance p<B → xs.length+3<B →
    m+k+limit+projection+ret+10<B → (∀ z∈xs,z<B) →
    Spec B (fun σ => NativeRoundedQuery.Data k state a σ ∧ σ.vars "algorithm.roundWidth"=v ∧
      σ.vars "graph.n"=m ∧ σ.vars "round.limit"=limit ∧
      xs.length≤(σ.arrs "vm.input").length ∧ T<(σ.arrs "vm.addresses").length ∧
      T<(σ.arrs "vm.values").length ∧ T<(σ.arrs "vm.output").length ∧
      3*(n*n)≤(σ.arrs "round.shape").length ∧ 3*n≤(σ.arrs "round.center").length)
      (command p projection ret) (fun _ τ => Prefix (NativeRoundedQuery.shape (update k state a)) "round.shape" τ ∧
        Prefix (NativeRoundedQuery.center (update k state a)) "round.center" τ ∧
        τ.vars "vec.n"=n ∧ Output m k limit projection ret τ)
      (NativeRoundedUpdate.timeBound p c n h k+16) := by
  obtain ⟨p,c,hc,hupdate⟩ := NativeRoundedUpdate.exists_program
  refine ⟨p,c,hc,?_⟩
  intro n m k h limit projection ret hn hh state a hA ha hx hpos B v hv
  dsimp only
  intro hB hT hp hlen hscalar hwords
  have hvB : v<B := by
    have hpow : 2^v≤(2^v)^2 := by simpa only [pow_two] using Nat.le_mul_self (2^v)
    have hvp : v<2^v := Nat.lt_two_pow_self
    nlinarith only [hB,hpow,hvp]
  rintro σ ⟨hd,hw,hm,hl,hinput,haddr,hvalue,houtput,hshape,hcenter⟩
  let ν := σ.setVar "vm.width" v
  have r0 : Run B (.assign "vm.width" (.var "algorithm.roundWidth")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hw.symm,hw ▸ hvB⟩)
  obtain ⟨μ,r1,p1⟩ := hupdate n k h hn hh state a hA ha hx hpos B v hv hB hT hp hlen hwords ν
    ⟨NativeRoundedQuery.frame r0 hd (by decide) (by decide) (by decide) (by decide) (by decide),by simp [ν],
      by rwa [RamFrames.run_array_length r0],by rwa [RamFrames.run_array_length r0],
      by rwa [RamFrames.run_array_length r0],by rwa [RamFrames.run_array_length r0],
      by rwa [RamFrames.run_array_length r0],by rwa [RamFrames.run_array_length r0]⟩
  have hm1 : μ.vars "graph.n"=m := (r1.frame_var _ (update_variable p _ (by decide) (by decide) (by decide) (by decide))).trans
    ((r0.frame_var _ (by decide)).trans hm)
  have hl1 : μ.vars "round.limit"=limit := (r1.frame_var _ (update_variable p _ (by decide) (by decide) (by decide) (by decide))).trans
    ((r0.frame_var _ (by decide)).trans hl)
  obtain ⟨τ,r2,p2⟩ := finish_spec B m k limit projection ret hscalar μ ⟨hm1,p1.2.2.2,hl1⟩
  refine ⟨τ,(r0.seq (r1.seq r2)).mono (by omega),?_,?_,?_,p2⟩
  · simpa only [Prefix,r2.frame_arr "round.shape" (by simp [finish,NativeAttemptReply.noneCommand,Com.warrs])] using p1.1
  · simpa only [Prefix,r2.frame_arr "round.center" (by simp [finish,NativeAttemptReply.noneCommand,Com.warrs])] using p1.2.1
  · exact (r2.frame_var _ (by simp [finish,NativeAttemptReply.noneCommand,Com.wvars])).trans p1.2.2.1

end Lax263307Proofs.NativeRoundedControl
