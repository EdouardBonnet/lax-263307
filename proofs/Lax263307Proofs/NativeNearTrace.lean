import Lax263307Proofs.NativeRoundTrace

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNearTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeCoreMachine NativeMachineSegment NativeSignedArithmetic NativeCatalogMetadata

/-- The nearby point is stored before the native conditioning search.
All catalog, graph and moment data needed by the next phase survive. -/
theorem conditioning_segment (B M n r k p : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin (N n r) → ℚ)
    (hn : 0<n) (hp : 0<p) (hM : 1≤M)
    (hN : 3*N n r+10<B) (hs : 3*(n*n)+3*n+r+10<B) (hm : 2^n<B)
    (hB : 2*M^2+3<B) (hH : 2*(NativeQuadraticSum.height M n)^2+3<B)
    (hx : ∀ i,Bounded M (x i))
    (htest : NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
      M (NativeQuadraticSum.height M n)<B)
    (hfloor : NativeConditioningFloor.base n p+NativeConditioningFloor.base n p^r+n+p+r+10<B)
    (σ : Env) (hd : NativeMomentAccess.Data G r σ)
    (hpoint : Prefix (encodeVector x) "lp.word" σ)
    (hkσ : σ.vars "conditioning.k"=k) (hpσ : σ.vars "conditioning.p"=p)
    (hroom : 3*n+3*(n*n)<(σ.arrs "lp.word").length)
    (hcopy : 3*n≤(σ.arrs "cut.source").length) (hsum : 3*(n*n)≤(σ.arrs "sum.input").length)
    (hstore : 3*N n r≤(σ.arrs "near.moments").length)
    (hr : σ.vars "machine.running"=1) (hphase : σ.vars "machine.phase"=6) :
    ∃ τ,Segment B (phases cfg) 1 (48*N n r+NativeHeavySearch.cost M n r+14) σ τ ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=7 ∧
      NativeConditioningEntry.Data G (MomentLP.decode x) τ ∧
      NativeHeavySearch.Output (findHeavyConditioning G k p (MomentLP.decode x)) τ := by
  obtain ⟨ν,r1,p1⟩ := NativeMomentStorage.command_spec B M n r x hN (by nlinarith) hx σ
    ⟨hpoint,hd.1.2.2.1,hd.1.2.1,hstore⟩
  have data : NativeConditioningEntry.Data G (MomentLP.decode x) ν :=
    ⟨p1.1,by simpa only [Prefix,r1.frame_arr "catalog.card" (by decide)] using hd.2.1,
      by simpa only [Prefix,r1.frame_arr "search.graph" (by decide)] using hd.1.2.2.2.1,
      (r1.frame_var _ (by decide)).trans hd.1.1,(r1.frame_var _ (by decide)).trans hd.2.2.2,
      by simpa only [RamFrames.run_array_length r1] using hroom,
      by simpa only [RamFrames.run_array_length r1] using hcopy,
      by simpa only [RamFrames.run_array_length r1] using hsum⟩
  have hy : ∀ T,Bounded M (MomentLP.decode x T) := fun T => hx ((CoordinateCatalog.indexing n r).symm T)
  obtain ⟨μ,r2,p2⟩ := NativeHeavySearch.command_spec B M n r k p G (MomentLP.decode x)
    hn hp hM hN hs hm hB hH hy htest hfloor ν
    ⟨data,(r1.frame_var _ (by decide)).trans hkσ,(r1.frame_var _ (by decide)).trans hpσ⟩
  let τ := μ.setVar "machine.phase" 7
  have r3 : Run B (go 7) μ τ 2 := Run.assign (evalB_lit (show 7<B by omega))
  have run : Run B (Com.seq NativeMomentStorage.command (Com.seq NativeHeavySearch.command (go 7))) σ τ
      (48*N n r+NativeHeavySearch.cost M n r+14) := (r1.seq (r2.seq r3)).mono (by omega)
  refine ⟨τ,NativeMachineSegment.phase hr ⟨6,by change 6<16; decide⟩ hphase run,?_,by simp [τ],?_,?_⟩
  · exact (run.frame_var _ (by decide)).trans hr
  · exact NativeConditioningEntry.frame r3 p2.1 (by intro s hs; simp [go,Com.warrs])
      (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
          rcases hs with rfl|rfl|rfl <;> decide)
  · cases hsel : findHeavyConditioning G k p (MomentLP.decode x) <;>
      simpa [hsel,NativeHeavySearch.Output,τ] using p2.2

private theorem value {B x : ℕ} {s : String} {σ : Env} (h : σ.vars s=x) (hx : x<B) :
    (Expr.var s).evalB B σ=some x := by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem none_segment (B n : ℕ) (cfg : Config) (hB : n+19<B)
    (σ : Env) (hn : σ.vars "graph.n"=n)
    (ho : NativeHeavySearch.Output (none : Option (Finset (Fin n))) σ)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=7) :
    ∃ τ,Segment B (phases cfg) 1 10 σ τ ∧ NativeRoundTrace.Stopped (none : Option (Finset (Fin n))) τ := by
  obtain ⟨τ,rr,po⟩ := NativeAttemptReply.none_spec B n 14 hB σ hn
  have ht : (Cond.eq (.var "conditioning.found") (.lit 1)).evalB B σ=some false :=
    evalB_condEq (value ho (by omega)) (evalB_lit (show 1<B by omega))
  have run : Run B conditioningReply σ τ 10 :=
    (Run.ite_false (c:=.seq (.assign "conditioning.mask" (.var "conditioning.choice"))
      (.seq NativeNearCosts.command (go 8))) ht rr).mono (by simp [Cond.size,Expr.size])
  exact ⟨τ,NativeMachineSegment.phase hr ⟨7,by change 7<16; decide⟩ hp run,
    (rr.frame_var _ (by decide)).trans hr,po.2.2,po.2.1⟩

/-- The selected conditioning mask is copied to the actual cost routine's
input variable, and its complete rational cost vector is then stored. -/
theorem some_segment (B M n r : ℕ) (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) (hM : 1≤M) (hA : A.card≤r)
    (hN : 3*N n r+10<B) (hn : 3*n+3<B) (hm : 2^n<B) (hB : 2*M^2+3<B)
    (hy : ∀ T,Bounded M (y T)) (σ : Env) (hd : NativeConditioningEntry.Data G y σ)
    (ho : NativeHeavySearch.Output (some A) σ)
    (hroom : 3*n<(σ.arrs "lp.word").length) (hcosts : 3*n≤(σ.arrs "near.costs").length)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=7) :
    ∃ τ,Segment B (phases cfg) 1 ((17*N n r+72*(M^2).size+270)*n+17*N n r+67) σ τ ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=8 ∧
      NativeNearCosts.Data y A τ ∧ Prefix (encodeVector (NativeNearCosts.values y A)) "near.costs" τ := by
  let ν := σ.setVar "conditioning.mask" (NativeMasks.mask A)
  have r1 : Run B (.assign "conditioning.mask" (.var "conditioning.choice")) σ ν 2 :=
    Run.assign (value ho.2 ((NativeMasks.mask_bound A).trans hm))
  obtain ⟨μ,r2,p2⟩ := NativeNearCosts.command_spec B M n r y A hM hA hN hn hm hB hy ν
    ⟨⟨by simpa [NativeMomentValue.Context,Prefix,ν] using hd.moments,by simp [ν],by simpa [ν] using hd.order⟩,
      hroom,hcosts⟩
  let τ := μ.setVar "machine.phase" 8
  have r3 : Run B (go 8) μ τ 2 := Run.assign (evalB_lit (show 8<B by omega))
  have ht : (Cond.eq (.var "conditioning.found") (.lit 1)).evalB B σ=some true :=
    evalB_condEq (value ho.1 (by omega)) (evalB_lit (show 1<B by omega))
  have run : Run B conditioningReply σ τ ((17*N n r+72*(M^2).size+270)*n+17*N n r+67) :=
    (Run.ite_true (d:=NativeAttemptReply.noneCommand 14) ht (r1.seq (r2.seq r3))).mono
      (by simp [Cond.size,Expr.size]; omega)
  refine ⟨τ,NativeMachineSegment.phase hr ⟨7,by change 7<16; decide⟩ hp run,
    (run.frame_var _ (by decide)).trans hr,by simp [τ],?_,p2.2⟩
  exact NativeNearCosts.frame r3 p2.1 (by intro s hs; simp [go,Com.warrs])
    (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
        rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;> decide)

end Lax263307Proofs.NativeNearTrace
