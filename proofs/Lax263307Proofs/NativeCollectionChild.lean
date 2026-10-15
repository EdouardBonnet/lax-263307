import Lax263307Proofs.NativeCollectionContext

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCollectionChild

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeCoreMachine NativeMachineSegment NativeMasks NativeCollectionContext

private theorem none_order {B K : ℕ} {σ τ : Env}
    (rr : Run B (NativeComponentControl.childReply 9 13) σ τ K)
    (hB : 1<B) (htag : σ.vars "recursion.return.tag"=0) :
    τ.vars "graph.n"=σ.vars "graph.n" := by
  have ht : (Cond.eq (.var "recursion.return.tag") (.lit 1)).evalB B σ=some false :=
    evalB_condEq (by rw [evalB_var_iff]; exact ⟨htag.symm,htag ▸ (by omega)⟩)
      (evalB_lit hB)
  obtain ⟨cost,hcost,step⟩ := rr
  cases step with
  | ite_true he _ => rw [ht] at he; cases he
  | ite_false _ step =>
    have r : Run B (NativeOracleCut.failedChild 13) σ τ _ := ⟨_,Nat.le_refl _,step⟩
    exact r.frame_var _ (by decide)

/-- Recursive execution required only at the actual child entry. -/
def Recursive {n : ℕ} (B S fuel childSteps childTime : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (target : ℕ) (front : List ℕ) (σ : Env) (answer : Option (Finset (Fin C.card))) : Prop :=
  ∀ saved entry,
      Run B (.seq NativeChildGraph.command (go 12)) σ saved (36*(C.card*C.card)+12) →
      Segment B (phases cfg) 1
        ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(C.card*C.card)+36) σ entry →
      Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" entry →
      entry.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length →
      Prefix (NativeWeightReduction.adjacency (ComputedSeparators.restriction G C)) "search.graph" entry →
      entry.vars "graph.n"=C.card → entry.vars "node.k"=target → entry.vars "recursion.fuel"=fuel →
      entry.vars "machine.running"=1 → entry.vars "machine.phase"=1 →
      ∃ done steps total,Segment B (phases cfg) steps total entry done ∧ steps≤childSteps ∧ total≤childTime ∧
        NativeRoundTrace.Stopped answer done ∧
        Prefix (front++NativeRecursionFrame.words (frameArrays cfg) (frameScalars cfg) saved) "recursion.frames" done ∧
        done.vars "stack.words"=front.length+S*(frameArrays cfg).length+(frameScalars cfg).length ∧
        done.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length ∧ done.vars "recursion.stride"=S

/-- This executes the actual call, pop, and component reply. The sole
recursive premise concerns the actual smaller-fuel entry produced by the
call. In particular, restoration of the parent context and construction of
the failed child's target-minus-one normal are conclusions. -/
theorem child_iteration {n : ℕ} (B S D k r fuel i target childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
    (parts : List (Finset (Fin n))) (A C U : Finset (Fin n))
    (extent : String → ℕ) (front : List ℕ) (answer : Option (Finset (Fin C.card)))
    (hB : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+
      n*n+n+i+target+fuel+3*NativeCatalogMetadata.N n r+50<B)
    (hm : 2^n<B) (hext : ∀ a∈frameArrays cfg,extent a=S)
    (hstack : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤extent "recursion.frames")
    (hchild : C.card*C.card≤extent "child.graph") (hsearch : C.card*C.card≤extent "search.graph")
    (hbits : C.card≤extent "subset.bits")
    (hlp : 3*NativeCatalogMetadata.N n r≤extent "lp.input")
    (hnormal : 3*NativeCatalogMetadata.N n r≤extent "round.normal")
    (σ : Env) (hc : Context B D k r fuel S G x parts A extent front σ)
    (hd : NativeRestrictionRead.Data G (fun v => (x v : ℚ)) C σ)
    (hmask : σ.vars "component.mask"=mask C) (htarget : σ.vars "component.target"=target)
    (hi : σ.vars "component.i"=i) (hu : σ.vars "component.union"=mask U)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=11)
    (recursive : Recursive B S fuel childSteps childTime cfg G C target front σ answer) :
    ∃ τ steps total,Segment B (phases cfg) steps total σ τ ∧ steps≤childSteps+3 ∧
      total≤((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(C.card*C.card)+36)+
        childTime+((16*S+16)*(frameArrays cfg).length+7*(frameScalars cfg).length+12)+
        ((45*C.card+38)+((28*n+104)*NativeCatalogMetadata.N n r+30)) ∧
      NativeCollectionAnchor.Anchor σ τ ∧
      match (generalizing := false) answer with
      | some I => NativeCollectionTrace.At (Context B D k r fuel S G x parts A extent front)
          (i+1) (U∪I.image (ComputedSeparators.label C)) τ
      | none => NativeCollectionTrace.ResultOutput (Context B D k r fuel S G x parts A extent front)
          (fun C u τ => Prefix (NativeRoundedQuery.normal (RationalCutBuffer.integerNormal
            (RoundedOracleSearch.rationalNormal (NativeComponentNormal.normal (r:=r) A C u)))) "round.normal" τ)
          (.cut C (target-1)) τ := by
  obtain ⟨saved,entry,snapshot,hsaved,rsaved,psaved,call,hfront,hwords,hgraph,horder,hk,hfuel,rentry,pentry⟩ :=
    NativeChildTrace.call_segment B S target fuel cfg G (fun v => (x v : ℚ)) C front (by omega) σ
      hc.bounded hd hc.stack hc.cursor hc.width
      (by intro a ha; rw [hc.lengths]; exact hext a ha)
      (by rw [hc.lengths]; exact hstack) (by rw [hc.lengths]; exact hchild)
      (by rw [hc.lengths]; exact hsearch) htarget hc.depth hr hp
  have csaved := NativeCollectionContext.frame snapshot hc (by decide) (by decide)
  obtain ⟨done,s,t,recur,hs,ht,reply,stackDone,wordsDone,lengthDone,strideDone⟩ :=
    recursive saved entry snapshot call hfront hwords hgraph horder hk hfuel rentry pentry
  obtain ⟨ν,returned,frontν,wordsν,runningν,phaseν,replyν,varsν,arraysν⟩ :=
    NativeChildExecution.returned_segment B S cfg front σ saved entry done answer 1
      ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(C.card*C.card)+36) s t
      (36*(C.card*C.card)+12) snapshot hsaved
      (by intro a ha; rw [csaved.lengths]; exact hext a ha) (by omega) rsaved psaved call recur reply
      ⟨stackDone,wordsDone,lengthDone,strideDone⟩
  have savedAnchor := NativeCollectionAnchor.frame snapshot (NativeCollectionAnchor.refl σ) (by decide) (by decide)
  have returnedAnchor := NativeCollectionAnchor.restored savedAnchor varsν arraysν
  have cν := NativeCollectionContext.restored csaved returned hc.bounded hc.lengths varsν arraysν frontν wordsν
  have indexν : ν.vars "component.i"=i :=
    (varsν _ (by decide)).trans ((snapshot.frame_var _ (by decide)).trans hi)
  have unionν : ν.vars "component.union"=mask U :=
    (varsν _ (by decide)).trans ((snapshot.frame_var _ (by decide)).trans hu)
  have maskν : ν.vars "component.mask"=mask C :=
    (varsν _ (by decide)).trans ((snapshot.frame_var _ (by decide)).trans hmask)
  have targetν : ν.vars "component.target"=target :=
    (varsν _ (by decide)).trans ((snapshot.frame_var _ (by decide)).trans htarget)
  have countν : ν.vars "restrict.count"=C.card :=
    (varsν _ (by decide)).trans ((snapshot.frame_var _ (by decide)).trans hd.count)
  have labelsν : Prefix (NativeRestrictionOrder.words C) "restrict.vertices" ν := by
    simpa only [Prefix,arraysν "restrict.vertices" (by decide),
      snapshot.frame_arr "restrict.vertices" (by decide)] using hd.labels
  cases answer with
  | some I =>
    obtain ⟨τ,last,orderτ,indexτ,unionτ,runningτ,phaseτ⟩ := NativeComponentTrace.child_some_segment B i cfg C U I
      (by omega) hm ν ⟨replyν.1,cν.order,countν,replyν.2,labelsν,
        by rw [cν.lengths]; exact hbits,indexν,unionν⟩ runningν phaseν
    have rr := NativeMachineFrame.single_run last ⟨12,by change 12<16; decide⟩ phaseν
    change Run B (NativeComponentControl.childReply 9 13) ν τ _ at rr
    refine ⟨τ,_,_,NativeMachineSegment.append returned last,by omega,by omega,
      NativeCollectionAnchor.frame rr returnedAnchor (by decide) (by decide),
      NativeCollectionContext.frame_order rr cν orderτ (by decide) (by decide),indexτ,unionτ,runningτ,phaseτ⟩
  | none =>
    obtain ⟨τ,last,normalτ,runningτ,phaseτ⟩ := NativeComponentTrace.child_none_segment B r cfg A C target
      (by omega) hm ν ⟨replyν,⟨cν.order,cν.dimension,cν.catalog,cν.conditioning,maskν,targetν⟩,
        cν.bounded.2.1,by rw [cν.lengths]; exact hlp,by rw [cν.lengths]; exact hnormal⟩ runningν phaseν
    have rr := NativeMachineFrame.single_run last ⟨12,by change 12<16; decide⟩ phaseν
    change Run B (NativeComponentControl.childReply 9 13) ν τ _ at rr
    refine ⟨τ,_,_,NativeMachineSegment.append returned last,by omega,by omega,
      NativeCollectionAnchor.frame rr returnedAnchor (by decide) (by decide),
      NativeCollectionContext.frame_order rr cν ((none_order rr (by omega) replyν).trans cν.order)
        (by decide) (by decide),runningτ,phaseτ,normalτ⟩

end Lax263307Proofs.NativeCollectionChild
