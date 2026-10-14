import Lax263307Proofs.NativeRoundTrace
import Lax263307Proofs.NativeOracleScalars

namespace Lax263307Proofs.NativeProjectionTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment NativeSignedArithmetic

theorem oracle_variable (p : Lax808846.Ram.Program) (coeff : List ℕ) (s : String)
    (hd : s∉NativeDistanceInput.command.wvars) (ho : s∉NativeOracleScalars.reserved)
    (ht : s∉NativeProjectionTolerance.command.wvars) (hr : s∉NativeProjectionResult.command.wvars) :
    s∉(NativeProjectionOracle.command p coeff).wvars := by
  simpa only [NativeProjectionOracle.command,NativeDistanceOracle.command,Com.wvars,List.mem_append,not_or]
    using And.intro (And.intro hd (NativeOracleScalars.command_variable p coeff s ho)) (And.intro ht hr)

/-- This is exactly the input contract supplied by the checked, fixed LP
invocation theorem. The buffer bounds are unchanged by preparation. -/
def InvocationInput {m N : ℕ} (P : Program ℚ m N) (x : Fin N → ℚ) (ρ : ℚ)
    (oracleTime : ℕ) (σ : Env) : Prop :=
  Prefix (encodeProgram P) "lp.input" σ ∧ Prefix (encodeVector x) "projection.center" σ ∧
  Prefix (encodeRational ρ) "projection.tolerance" σ ∧
  NativeDistanceData.wordLength m N<(σ.arrs "lp.word").length ∧
  (encodeProgram (DistanceProjection.distanceProgram P x)).length<(σ.arrs "vm.input").length ∧
  oracleTime<(σ.arrs "vm.addresses").length ∧ oracleTime<(σ.arrs "vm.values").length ∧
  oracleTime<(σ.arrs "vm.output").length

/-- Execute phase 4 of the fixed controller: restore the cached LP,
prepare the actual center/tolerance, invoke the selected LP program, and
enter phase 5. The invocation premise is supplied by
NativeProjectionOracle.exists_invocation, not by a new external assumption. -/
theorem projection_segment {m N : ℕ} (B M n D R : ℕ) (cfg : Config)
    (P : Program ℚ m N) (x : Fin N → ℚ) (result : RationalProjection.Outcome N)
    (oracleTime callCost : ℕ)
    (call : Spec B (InvocationInput P (ProjectedOracle.raw x) (NativeNodeTolerance.tolerance n D R) oracleTime)
      (NativeProjectionOracle.command cfg.lp cfg.lpWidth) (fun _ τ => NativeProjectionResult.Output result τ ∧ τ.vars "projection.n"=N) callCost)
    (hn : 0<n) (hD : 0<D) (hR : 0<R)
    (hLP : (encodeProgram P).length+2<B) (hB : 2*M^2+3<B)
    (hshape : 4*N+5<B) (hscale : 4*N≤M) (hx : ∀ j,Bounded M (x j))
    (htol : NativeNodeTolerance.guard n D R<B) :
    ∀ σ, NativeProjectionCenter.Context x σ → NativeNodeTolerance.Context n D R σ →
      Prefix (encodeProgram P) "moment.program" σ → σ.vars "node.programLength"=(encodeProgram P).length →
      NativeArrayBounds.Bounded B σ → (encodeProgram P).length≤(σ.arrs "lp.input").length →
      3*N<(σ.arrs "lp.word").length → 3*N≤(σ.arrs "projection.center").length →
      3≤(σ.arrs "lp.word").length → 3≤(σ.arrs "projection.tolerance").length →
      NativeDistanceData.wordLength m N<(σ.arrs "lp.word").length →
      (encodeProgram (DistanceProjection.distanceProgram P (ProjectedOracle.raw x))).length<(σ.arrs "vm.input").length →
      oracleTime<(σ.arrs "vm.addresses").length → oracleTime<(σ.arrs "vm.values").length →
      oracleTime<(σ.arrs "vm.output").length →
      σ.vars "machine.running"=1 → σ.vars "machine.phase"=4 →
      ∃ τ,Segment B (phases cfg) 1
        (16*(encodeProgram P).length+(36*M.size+124)*N+135+callCost+2) σ τ ∧
        τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=5 ∧ NativeProjectionResult.Output result τ ∧ τ.vars "projection.n"=N := by
  intro σ hc ht hp hlen hb hinput hword hcenter hword3 htol3 hdist hvm ha hv ho hr hphase
  obtain ⟨ν,r1,p1⟩ := NativeProjectionPrepare.command_spec B M n D R m N P x hn hD hR hLP hB
    hshape hscale hx htol σ ⟨hc,ht,hp,hlen,hb,hinput,hword,hcenter,hword3,htol3⟩
  obtain ⟨μ,r2,p2⟩ := call ν ⟨p1.2.2.1,p1.2.2.2.1,p1.2.2.2.2,
    by rw [RamFrames.run_array_length r1]; exact hdist,
    by rw [RamFrames.run_array_length r1]; exact hvm,
    by rw [RamFrames.run_array_length r1]; exact ha,
    by rw [RamFrames.run_array_length r1]; exact hv,
    by rw [RamFrames.run_array_length r1]; exact ho⟩
  let τ := μ.setVar "machine.phase" 5
  have r3 : Run B (go 5) μ τ 2 := Run.assign (evalB_lit (show 5<B by omega))
  have rr : Run B ((phases cfg)[4]'(by change 4<16; decide)) σ τ
      (16*(encodeProgram P).length+(36*M.size+124)*N+135+callCost+2) := by
    simpa only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,Nat.add_assoc] using r1.seq (r2.seq r3)
  refine ⟨τ,NativeMachineSegment.phase hr ⟨4,by change 4<16; decide⟩ hphase rr,?_,by simp [τ],?_,?_⟩
  · exact (r3.frame_var _ (by decide)).trans ((r2.frame_var _
      (oracle_variable _ _ _ (by decide) (by decide) (by decide) (by decide))).trans
      ((r1.frame_var _ (by decide)).trans hr))
  · cases result <;> simpa [NativeProjectionResult.Output,τ,Prefix] using p2.1
  · simpa [τ] using p2.2

private theorem value {B x : ℕ} {s : String} {σ : Env} (h : σ.vars s=x) (hx : x<B) :
    (Expr.var s).evalB B σ=some x := by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem near_segment {N : ℕ} (B : ℕ) (cfg : Config) (x : Fin N → ℚ) (hB : 7<B)
    (σ : Env) (ho : NativeProjectionResult.Output (.near x) σ)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=5) :
    ∃ τ,Segment B (phases cfg) 1 6 σ τ ∧ τ=σ.setVar "machine.phase" 6 ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=6 ∧ NativeProjectionResult.Output (.near x) τ := by
  let τ := σ.setVar "machine.phase" 6
  have rr : Run B (go 6) σ τ 2 := Run.assign (evalB_lit (show 6<B by omega))
  have ht : (Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some true :=
    evalB_condEq (value ho.1 (by omega)) (evalB_lit (show 0<B by omega))
  have run : Run B projectionReply σ τ 6 :=
    (Run.ite_true (d:=.ite (.eq (.var "projection.kind") (.lit 1))
      (NativeOracleCut.far 13) (NativeAttemptReply.noneCommand 14)) ht rr).mono (by simp [Cond.size,Expr.size])
  refine ⟨τ,NativeMachineSegment.phase hr ⟨5,by change 5<16; decide⟩ hp run,rfl,?_,by simp [τ],?_⟩
  · simpa [τ] using hr
  · simpa [τ,NativeProjectionResult.Output,Prefix] using ho

theorem reject_segment {n N : ℕ} (B : ℕ) (cfg : Config) (hB : n+19<B)
    (σ : Env) (ho : NativeProjectionResult.Output (.reject : RationalProjection.Outcome N) σ)
    (hn : σ.vars "graph.n"=n) (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=5) :
    ∃ τ,Segment B (phases cfg) 1 14 σ τ ∧ NativeRoundTrace.Stopped (none : Option (Finset (Fin n))) τ := by
  obtain ⟨τ,rr,po⟩ := NativeAttemptReply.none_spec B n 14 hB σ hn
  have ht0 : (Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some false :=
    evalB_condEq (value ho (by omega)) (evalB_lit (show 0<B by omega))
  have ht1 : (Cond.eq (.var "projection.kind") (.lit 1)).evalB B σ=some false :=
    evalB_condEq (value ho (by omega)) (evalB_lit (show 1<B by omega))
  have run : Run B projectionReply σ τ 14 :=
    (Run.ite_false (c:=go 6) ht0 (Run.ite_false (c:=NativeOracleCut.far 13) ht1 rr)).mono
      (by simp [Cond.size,Expr.size])
  exact ⟨τ,NativeMachineSegment.phase hr ⟨5,by change 5<16; decide⟩ hp run,
    (rr.frame_var _ (by decide)).trans hr,po.2.2,po.2.1⟩

theorem far_segment {N : ℕ} (B M : ℕ) (cfg : Config) (a : Fin N → ℚ) (β : ℚ)
    (hB : M*RationalCutBuffer.denominator a+M+RationalCutBuffer.denominator a+3*N+23<B)
    (ha : ∀ j,Bounded M (a j)) (σ : Env)
    (ho : NativeProjectionResult.Output (.far a β) σ) (hn : σ.vars "projection.n"=N)
    (hb : NativeArrayBounds.Bounded B σ) (hc : 3*N≤(σ.arrs "cut.source").length)
    (hw : 3*N<(σ.arrs "lp.word").length) (hnormal : 3*N≤(σ.arrs "round.normal").length)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=5) :
    ∃ τ,Segment B (phases cfg) 1 (193*N+48) σ τ ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=13 ∧
      Prefix (NativeRoundedQuery.normal (RationalCutBuffer.integerNormal a)) "round.normal" τ := by
  obtain ⟨τ,rr,po⟩ := NativeOracleCut.far_spec B M N 13 a hB ha σ ⟨hb,ho.2.1,hn,hc,hw,hnormal⟩
  have ht0 : (Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some false :=
    evalB_condEq (value ho.1 (by omega)) (evalB_lit (show 0<B by omega))
  have ht1 : (Cond.eq (.var "projection.kind") (.lit 1)).evalB B σ=some true :=
    evalB_condEq (value ho.1 (by omega)) (evalB_lit (show 1<B by omega))
  have run : Run B projectionReply σ τ (193*N+48) :=
    (Run.ite_false (c:=go 6) ht0 (Run.ite_true (d:=NativeAttemptReply.noneCommand 14) ht1 rr)).mono
      (by simp [Cond.size,Expr.size]; omega)
  exact ⟨τ,NativeMachineSegment.phase hr ⟨5,by change 5<16; decide⟩ hp run,
    (rr.frame_var _ (by decide)).trans hr,po.2,po.1⟩

end Lax263307Proofs.NativeProjectionTrace
