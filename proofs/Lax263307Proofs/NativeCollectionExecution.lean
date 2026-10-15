import Lax263307Proofs.NativeCollectionChild

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCollectionExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedRounding NativeCoreMachine NativeMachineSegment NativeMasks NativeCollectionContext

/-- Collection context together with all untouched parent data. -/
def Invariant {n : ℕ} (B D k r fuel S : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (parts : List (Finset (Fin n))) (A : Finset (Fin n))
    (extent : String → ℕ) (front : List ℕ) (base σ : Env) : Prop :=
  Context B D k r fuel S G x parts A extent front σ ∧ NativeCollectionAnchor.Anchor base σ

/-- Exact normal stored on the first failed component. -/
def Cut {n : ℕ} (r : ℕ) (A C : Finset (Fin n)) (u : ℕ) (σ : Env) : Prop :=
  Prefix (NativeRoundedQuery.normal (RationalCutBuffer.integerNormal
    (RoundedOracleSearch.rationalNormal (NativeComponentNormal.normal (r:=r) A C u)))) "round.normal" σ

def partCost (cfg : Config) (n r S h childTime : ℕ) : ℕ :=
  43*n+37+NativeComponentDecision.timeBound n h+
    ((16*S+8)*(frameArrays cfg).length+7*(frameScalars cfg).length+52*(n*n)+36)+
    childTime+((16*S+16)*(frameArrays cfg).length+7*(frameScalars cfg).length+12)+
    ((45*n+38)+((28*n+104)*NativeCatalogMetadata.N n r+30))

/-- The native list index selects precisely the functional part at this
position, even for an order containing repeated indices. -/
theorem part_at {n : ℕ} {ι : Type} (parts : ι → Finset (Fin n))
    (order pre : List ι) (i : ι) (suffix : List ι) (he : pre++i::suffix=order) :
    ∃ h : pre.length<(order.map parts).length,(order.map parts)[pre.length]=parts i := by
  have h : pre.length<(order.map parts).length := by
    rw [List.length_map,←he,List.length_append,List.length_cons]; omega
  refine ⟨h,?_⟩
  simp only [List.getElem_map]
  have ho : pre.length<order.length := by simpa only [List.length_map] using h
  have hi : order[pre.length]=i := by
    subst order
    simp
  rw [hi]

/-- Instantiate every collection iteration from the actual phase 9/10
handlers and the actual heavy call/pop/reply. The recursive premise is only
execution of smaller-fuel children, not execution of collection itself. -/
theorem iterations {n : ℕ} {ι : Type} (D k r fuel S h T childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
    (parts : ι → Finset (Fin n)) (order : List ι) (A : Finset (Fin n))
    (extent : String → ℕ) (front : List ℕ) (base : Env)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (hn : 0<n) (hD : 0<D) (hx : ∀ v,NativeSignedArithmetic.Bounded (2^h) (x v : ℚ))
    (w : ℕ) (hw : NativeComponentDecision.wordHeight n D k h≤w)
    (hparts : order.length≤n+1) (hm : 2^n<2^w)
    (hB : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+n*n+2*n+
      2*order.length+T+fuel+3*NativeCatalogMetadata.N n r+80<2^w)
    (htarget : ∀ i∈order,target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ))≤T)
    (hext : ∀ a∈frameArrays cfg,extent a=S)
    (hstack : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤extent "recursion.frames")
    (hchild : n*n≤extent "child.graph") (hsearch : n*n≤extent "search.graph")
    (hbits : n≤extent "subset.bits") (hlabels : n≤extent "restrict.vertices")
    (hword : 3*n<extent "lp.word") (hsum : 3*n≤extent "sum.input")
    (hlp : 3*NativeCatalogMetadata.N n r≤extent "lp.input")
    (hnormal : 3*NativeCatalogMetadata.N n r≤extent "round.normal")
    (recursive : ∀ i∈order,(1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈parts i,(x v : ℚ)) → ∀ σ,
      Invariant (2^w) D k r fuel S G x (order.map parts) A extent front base σ →
      NativeRestrictionRead.Data G (fun v => (x v : ℚ)) (parts i) σ →
      σ.vars "component.mask"=mask (parts i) →
      σ.vars "component.target"=target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ)) →
      σ.vars "machine.running"=1 → σ.vars "machine.phase"=11 →
      NativeCollectionChild.Recursive (2^w) S fuel childSteps childTime cfg G (parts i)
        (target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ))) front σ
        (child (parts i) (target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ))))) :
    NativeCollectionTrace.Iterations (2^w) cfg
      (Invariant (2^w) D k r fuel S G x (order.map parts) A extent front base) (Cut r A) parts
      (fun i => target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ))-1)
      (answer (n:=n) (1/(D : ℚ)) k (fun i => ∑ v∈parts i,(x v : ℚ))
        (fun i t => (child (parts i) t).map (fun I => I.image (ComputedSeparators.label (parts i)))))
      order (childSteps+5) (partCost cfg n r S h childTime) := by
  intro pre i suffix he U σ hin
  have hin0 : NativeCollectionTrace.At (Context (2^w) D k r fuel S G x (order.map parts) A extent front) pre.length U σ := ⟨hin.1.1,hin.2⟩
  obtain ⟨hidx,hpart⟩ := part_at parts order pre i suffix he
  have hlen : pre.length<order.length := by simpa only [List.length_map] using hidx
  have hi : i∈order := by rw [←he]; simp
  by_cases heavy : (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈parts i,(x v : ℚ))
  · obtain ⟨ν,first,contextν,dataν,maskν,indexν,unionν,targetν,runningν,phaseν,anchorFirst⟩ :=
      NativeCollectionContext.heavy_entry n D k r fuel S h cfg G x (order.map parts) A extent front
        hn hD hx w hw (by simpa only [List.length_map] using hparts) pre.length hidx
        (by simp only [List.length_map]; omega) hbits hlabels hword hsum
        (by simpa only [hpart] using heavy) U σ hin0
    rw [hpart] at dataν maskν targetν
    have anchorν := NativeCollectionAnchor.trans hin.1.2 anchorFirst
    have ht := htarget i hi
    have hc := NativeMaskUnpack.card_bound (parts i)
    have hsq : (parts i).card*(parts i).card≤n*n := Nat.mul_self_le_mul_self hc
    obtain ⟨τ,s,t,last,hs,htime,anchorLast,hout⟩ := NativeCollectionChild.child_iteration (2^w) S D k r fuel pre.length
      (target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ))) childSteps childTime cfg G x (order.map parts)
      A (parts i) U extent front (child (parts i) (target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ))))
      (by omega) hm hext hstack (hsq.trans hchild) (hsq.trans hsearch) (hc.trans hbits) hlp hnormal
      ν contextν dataν maskν targetν indexν unionν runningν phaseν
      (recursive i hi heavy ν ⟨contextν,anchorν⟩ dataν maskν targetν runningν phaseν)
    have anchorτ := NativeCollectionAnchor.trans anchorν anchorLast
    refine ⟨τ,2+s,43*n+33+NativeComponentDecision.timeBound n h+t,
      NativeMachineSegment.append first last,by omega,?_,?_⟩
    · dsimp only [partCost]
      omega
    · cases hreply : child (parts i) (target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ))) with
      | none =>
        simp only [answer,heavy,if_true,hreply,Option.map_none,NativeCollectionTrace.ResultOutput,Cut] at hout ⊢
        exact ⟨⟨hout.1,anchorτ⟩,hout.2⟩
      | some I =>
        simp only [answer,heavy,if_true,hreply,Option.map_some,NativeCollectionTrace.At] at hout ⊢
        exact ⟨⟨hout.1,anchorτ⟩,hout.2⟩
  · obtain ⟨τ,trace,hout,anchor⟩ := NativeCollectionContext.light_iteration n D k r fuel S h cfg G x
      (order.map parts) A extent front hn hD hx w hw (by simpa only [List.length_map] using hparts)
      pre.length hidx (by simp only [List.length_map]; omega) hbits hlabels hword hsum
      (by simpa only [hpart] using heavy) U σ hin0
    refine ⟨τ,2,43*n+37+NativeComponentDecision.timeBound n h,trace,by omega,?_,?_⟩
    · dsimp only [partCost]; omega
    · simp only [answer,heavy,if_false,Finset.union_empty,NativeCollectionTrace.At] at hout ⊢
      exact ⟨⟨hout.1,NativeCollectionAnchor.trans hin.1.2 anchor⟩,hout.2⟩

/-- The complete native collector now satisfies the functional collector
specification, with explicit transition and time bounds. -/
theorem collect_segment {n : ℕ} {ι : Type} [Fintype ι] (D k r fuel S h T childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
    (parts : ι → Finset (Fin n)) (order : List ι) (A : Finset (Fin n))
    (extent : String → ℕ) (front : List ℕ) (base : Env)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (complete : ∀ i,i∈order)
    (hn : 0<n) (hD : 0<D) (hx : ∀ v,NativeSignedArithmetic.Bounded (2^h) (x v : ℚ))
    (w : ℕ) (hw : NativeComponentDecision.wordHeight n D k h≤w)
    (hparts : order.length≤n+1) (hm : 2^n<2^w)
    (hB : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+n*n+2*n+
      2*order.length+T+fuel+3*NativeCatalogMetadata.N n r+80<2^w)
    (htarget : ∀ i∈order,target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ))≤T)
    (hext : ∀ a∈frameArrays cfg,extent a=S)
    (hstack : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤extent "recursion.frames")
    (hchild : n*n≤extent "child.graph") (hsearch : n*n≤extent "search.graph")
    (hbits : n≤extent "subset.bits") (hlabels : n≤extent "restrict.vertices")
    (hword : 3*n<extent "lp.word") (hsum : 3*n≤extent "sum.input")
    (hlp : 3*NativeCatalogMetadata.N n r≤extent "lp.input")
    (hnormal : 3*NativeCatalogMetadata.N n r≤extent "round.normal")
    (recursive : ∀ i∈order,(1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈parts i,(x v : ℚ)) → ∀ σ,
      Invariant (2^w) D k r fuel S G x (order.map parts) A extent front base σ →
      NativeRestrictionRead.Data G (fun v => (x v : ℚ)) (parts i) σ →
      σ.vars "component.mask"=mask (parts i) →
      σ.vars "component.target"=target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ)) →
      σ.vars "machine.running"=1 → σ.vars "machine.phase"=11 →
      NativeCollectionChild.Recursive (2^w) S fuel childSteps childTime cfg G (parts i)
        (target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ))) front σ
        (child (parts i) (target (1/(D : ℚ)) (∑ v∈parts i,(x v : ℚ)))))
    (σ : Env) (hin : NativeCollectionTrace.At (n:=n)
      (Invariant (2^w) D k r fuel S G x (order.map parts) A extent front base) 0 ∅ σ) :
    ∃ τ transitions total,Segment (2^w) (phases cfg) transitions total σ τ ∧
      transitions≤(childSteps+5)*order.length+1 ∧
      total≤partCost cfg n r S h childTime*order.length+10 ∧
      NativeCollectionTrace.ResultOutput
        (Invariant (2^w) D k r fuel S G x (order.map parts) A extent front base) (Cut r A)
        (collect order parts (1/(D : ℚ)) k (fun i => ∑ v∈parts i,(x v : ℚ))
          (fun i t => (child (parts i) t).map (fun I => I.image (ComputedSeparators.label (parts i))))) τ := by
  have actual := iterations D k r fuel S h T childSteps childTime cfg G x parts order A extent front base child
    hn hD hx w hw hparts hm hB htarget hext hstack hchild hsearch hbits hlabels hword hsum hlp hnormal recursive
  exact NativeCollectionTrace.collect_segment (2^w) cfg
    (Invariant (2^w) D k r fuel S G x (order.map parts) A extent front base) (Cut r A)
    parts (1/(D : ℚ)) k (fun i => ∑ v∈parts i,(x v : ℚ))
    (fun i t => (child (parts i) t).map (fun I => I.image (ComputedSeparators.label (parts i))))
    order complete (childSteps+5) (partCost cfg n r S h childTime) (by omega) hm
    (fun σ hc => by simpa only [List.length_map] using hc.1.count)
    (fun σ τ t rr hc => ⟨NativeCollectionContext.frame rr hc.1 (by decide) (by decide),
      NativeCollectionAnchor.frame rr hc.2 (by decide) (by decide)⟩) actual σ hin

end Lax263307Proofs.NativeCollectionExecution
