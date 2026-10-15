import Lax263307Proofs.NativeRoundTrace

namespace Lax263307Proofs.NativeComponentTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment NativeSignedArithmetic NativeMasks

private theorem value {B x : ℕ} {s : String} {σ : Env} (h : σ.vars s=x) (hx : x<B) :
    (Expr.var s).evalB B σ=some x := by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem load_segment (n D k h : ℕ) (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (hn : 0<n) (hD : 0<D) (hx : ∀ v,Bounded (2^h) (x v : ℚ))
    (w : ℕ) (hw : NativeComponentDecision.wordHeight n D k h≤w)
    (parts : List (Finset (Fin n))) (hparts : parts.length≤n+1) (i : ℕ) (hi : i<parts.length)
    (hB : i+parts.length+12<2^w) (σ : Env)
    (hin : σ.vars "graph.n"=n ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧
      Prefix (encodeVector (fun v => (x v : ℚ))) "near.costs" σ ∧ σ.vars "component.i"=i ∧
      Prefix (parts.map mask) "separator.pieces" σ ∧ n≤(σ.arrs "subset.bits").length ∧
      n≤(σ.arrs "restrict.vertices").length ∧ σ.vars "algorithm.D"=D ∧ σ.vars "conditioning.k"=k ∧
      3*n<(σ.arrs "lp.word").length ∧ 3*n≤(σ.arrs "sum.input").length)
    (hcount : σ.vars "component.count"=parts.length)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=9) :
    ∃ τ,Segment (2^w) (phases cfg) 1 (43*n+27+NativeComponentDecision.timeBound n h) σ τ ∧
      NativeRestrictionRead.Data G (fun v => (x v : ℚ)) parts[i] τ ∧
      τ.vars "component.mask"=mask parts[i] ∧ τ.vars "component.i"=i ∧
      τ.vars "component.target"=ComputedRounding.target (1/(D : ℚ)) (∑ v∈parts[i],(x v : ℚ)) ∧
      τ.vars "component.active"=(if (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈parts[i],(x v : ℚ)) then 1 else 0) ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=10 := by
  obtain ⟨μ,r1,p1⟩ := NativeComponentLoad.command_spec n D k h G x hn hD hx w hw parts hparts i hi σ hin
  let τ := μ.setVar "machine.phase" 10
  have r2 : Run (2^w) (go 10) μ τ 2 := Run.assign (evalB_lit (show 10<2^w by omega))
  have ht : (Cond.lt (.var "component.i") (.var "component.count")).evalB (2^w) σ=some true := by
    have hh := evalB_condLt (value hin.2.2.2.1 (show i<2^w by omega)) (value hcount (show parts.length<2^w by omega))
    simpa only [hi,decide_true] using hh
  have run : Run (2^w) component σ τ (43*n+27+NativeComponentDecision.timeBound n h) :=
    (Run.ite_true (d:=NativeComponentControl.finish 14) ht (r1.seq r2)).mono
      (by simp [Cond.size,Expr.size]; omega)
  refine ⟨τ,NativeMachineSegment.phase hr ⟨9,by change 9<16; decide⟩ hp run,?_,?_,?_,?_,?_,
    (run.frame_var _ (by decide)).trans hr,by simp [τ]⟩
  · exact NativeRestrictionRead.frame r2 p1.1 (by intro s hs; simp [go,Com.warrs])
      (by intro s hs; simp only [List.mem_cons,List.not_mem_nil,or_false] at hs; rcases hs with rfl|rfl <;> decide)
  · simpa [τ] using p1.2.1
  · simpa [τ] using p1.2.2.1
  · simpa [τ] using p1.2.2.2.1
  · simpa [τ] using p1.2.2.2.2


theorem active_segment (B : ℕ) (cfg : Config) (hB : 12<B) (σ : Env)
    (ha : σ.vars "component.active"=1) (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=10) :
    ∃ τ,Segment B (phases cfg) 1 6 σ τ ∧ τ=σ.setVar "machine.phase" 11 ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=11 := by
  let τ := σ.setVar "machine.phase" 11
  have rr : Run B (go 11) σ τ 2 := Run.assign (evalB_lit (show 11<B by omega))
  have ht : (Cond.eq (.var "component.active") (.lit 1)).evalB B σ=some true :=
    evalB_condEq (value ha (by omega)) (evalB_lit (show 1<B by omega))
  have run : Run B (.ite (.eq (.var "component.active") (.lit 1)) (go 11) (NativeComponentControl.advance 9)) σ τ 6 :=
    (Run.ite_true ht rr).mono (by simp [Cond.size,Expr.size])
  exact ⟨τ,NativeMachineSegment.phase hr ⟨10,by change 10<16; decide⟩ hp run,rfl,by simpa [τ] using hr,by simp [τ]⟩

theorem light_segment (B i : ℕ) (cfg : Config) (hB : i+12<B) (σ : Env)
    (ha : σ.vars "component.active"=0) (hi : σ.vars "component.i"=i)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=10) :
    ∃ τ,Segment B (phases cfg) 1 10 σ τ ∧ τ.vars "component.i"=i+1 ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=9 := by
  obtain ⟨τ,rr,po⟩ := NativeComponentControl.advance_spec B i 9 hB σ hi
  have ht : (Cond.eq (.var "component.active") (.lit 1)).evalB B σ=some false :=
    evalB_condEq (value ha (by omega)) (evalB_lit (show 1<B by omega))
  have run : Run B (.ite (.eq (.var "component.active") (.lit 1)) (go 11) (NativeComponentControl.advance 9)) σ τ 10 :=
    (Run.ite_false ht rr).mono (by simp [Cond.size,Expr.size])
  exact ⟨τ,NativeMachineSegment.phase hr ⟨10,by change 10<16; decide⟩ hp run,po.1,
    (rr.frame_var _ (by decide)).trans hr,po.2⟩

theorem child_some_segment {n : ℕ} (B i : ℕ) (cfg : Config) (C S : Finset (Fin n))
    (I : Finset (Fin C.card)) (hB : n+i+14<B) (hm : 2^n<B) (σ : Env)
    (hd : σ.vars "recursion.return.tag"=1 ∧ σ.vars "graph.n"=n ∧
      σ.vars "restrict.count"=C.card ∧ σ.vars "recursion.return.mask"=mask I ∧
      Prefix (NativeRestrictionOrder.words C) "restrict.vertices" σ ∧ C.card≤(σ.arrs "subset.bits").length ∧
      σ.vars "component.i"=i ∧ σ.vars "component.union"=mask S)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=12) :
    ∃ τ,Segment B (phases cfg) 1 (45*C.card+38) σ τ ∧ τ.vars "graph.n"=n ∧
      τ.vars "component.i"=i+1 ∧ τ.vars "component.union"=mask (S∪I.image (ComputedSeparators.label C)) ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=9 := by
  obtain ⟨τ,rr,po⟩ := NativeComponentControl.child_some_spec B i 9 13 C S I hB hm σ hd
  exact ⟨τ,NativeMachineSegment.phase hr ⟨12,by change 12<16; decide⟩ hp rr,
    po.1,po.2.1,po.2.2.1,(rr.frame_var _ (by decide)).trans hr,po.2.2.2⟩

theorem child_none_segment {n : ℕ} (B r : ℕ) (cfg : Config) (A C : Finset (Fin n)) (t : ℕ)
    (hB : n+t+3*NativeCatalogMetadata.N n r+23<B) (hm : 2^n<B) (σ : Env)
    (hd : σ.vars "recursion.return.tag"=0 ∧ NativeComponentNormal.Data r A C t σ ∧
      NativeArrayBounds.Bounded B σ ∧ 3*NativeCatalogMetadata.N n r≤(σ.arrs "lp.input").length ∧
      3*NativeCatalogMetadata.N n r≤(σ.arrs "round.normal").length)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=12) :
    ∃ τ,Segment B (phases cfg) 1 ((28*n+104)*NativeCatalogMetadata.N n r+30) σ τ ∧
      Prefix (NativeRoundedQuery.normal (RationalCutBuffer.integerNormal (RoundedOracleSearch.rationalNormal
        (NativeComponentNormal.normal (r:=r) A C (t-1))))) "round.normal" τ ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=13 := by
  obtain ⟨τ,rr,po⟩ := NativeComponentControl.child_none_spec B r 9 13 A C t hB hm σ hd
  exact ⟨τ,NativeMachineSegment.phase hr ⟨12,by change 12<16; decide⟩ hp rr,
    po.1,(rr.frame_var _ (by decide)).trans hr,po.2⟩

end Lax263307Proofs.NativeComponentTrace
