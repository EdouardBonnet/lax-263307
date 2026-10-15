import Lax263307Proofs.NativeCollectionTrace
import Lax263307Proofs.NativeChildExecution
import Lax263307Proofs.NativeMachineBounds
import Lax263307Proofs.NativeCollectionAnchor

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCollectionContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment NativeMasks

/-- The actual parent data held fixed while collecting components. The
array extents and stack prefix are included, so this context can be used
at the next child call as well as at the final failed-component cut. -/
structure Context {n : ℕ} (B D k r fuel stride : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
    (parts : List (Finset (Fin n))) (A : Finset (Fin n))
    (extent : String → ℕ) (front : List ℕ) (σ : Env) : Prop where
  order : σ.vars "graph.n"=n
  graph : Prefix (NativeWeightReduction.adjacency G) "search.graph" σ
  costs : Prefix (encodeVector (fun v => (x v : ℚ))) "near.costs" σ
  pieces : Prefix (parts.map mask) "separator.pieces" σ
  count : σ.vars "component.count"=parts.length
  denominator : σ.vars "algorithm.D"=D
  target : σ.vars "conditioning.k"=k
  dimension : σ.vars "catalog.count"=NativeCatalogMetadata.N n r
  catalog : Prefix (NativeCatalog.words n r) "catalog.mask" σ
  conditioning : σ.vars "conditioning.choice"=mask A
  bounded : NativeStateBounds.Bounded B σ
  lengths : ∀ a,(σ.arrs a).length=extent a
  stack : Prefix front "recursion.frames" σ
  cursor : σ.vars "stack.words"=front.length
  width : σ.vars "recursion.stride"=stride
  depth : σ.vars "recursion.fuel"=fuel+1

def scalars : List String := ["graph.n","component.count","algorithm.D",
  "conditioning.k","catalog.count","conditioning.choice","stack.words",
  "recursion.stride","recursion.fuel"]
def arrays : List String := ["search.graph","near.costs","separator.pieces",
  "catalog.mask","recursion.frames"]

theorem frame_order {n B D k r fuel stride K : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {x : Fin n → ℚ≥0}
    {parts : List (Finset (Fin n))} {A : Finset (Fin n)}
    {extent : String → ℕ} {front : List ℕ} {σ τ : Env} {c : Com}
    (rr : Run B c σ τ K) (hc : Context B D k r fuel stride G x parts A extent front σ)
    (hn : τ.vars "graph.n"=n)
    (hv : ∀ s∈scalars,s≠"graph.n" → s∉c.wvars) (ha : ∀ a∈arrays,a∉c.warrs) :
    Context B D k r fuel stride G x parts A extent front τ := by
  refine ⟨hn,?_,?_,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.count,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.denominator,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.target,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.dimension,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.conditioning,
    NativeStateBounds.run rr hc.bounded,?_,?_,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.cursor,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.width,
    (rr.frame_var _ (hv _ (by simp [scalars]) (by decide))).trans hc.depth⟩
  · simpa only [Prefix,rr.frame_arr "search.graph" (ha _ (by simp [arrays]))] using hc.graph
  · simpa only [Prefix,rr.frame_arr "near.costs" (ha _ (by simp [arrays]))] using hc.costs
  · simpa only [Prefix,rr.frame_arr "separator.pieces" (ha _ (by simp [arrays]))] using hc.pieces
  · simpa only [Prefix,rr.frame_arr "catalog.mask" (ha _ (by simp [arrays]))] using hc.catalog
  · intro a; rw [RamFrames.run_array_length rr]; exact hc.lengths a
  · simpa only [Prefix,rr.frame_arr "recursion.frames" (ha _ (by simp [arrays]))] using hc.stack

theorem frame {n B D k r fuel stride K : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {x : Fin n → ℚ≥0}
    {parts : List (Finset (Fin n))} {A : Finset (Fin n)}
    {extent : String → ℕ} {front : List ℕ} {σ τ : Env} {c : Com}
    (rr : Run B c σ τ K) (hc : Context B D k r fuel stride G x parts A extent front σ)
    (hv : ∀ s∈scalars,s∉c.wvars) (ha : ∀ a∈arrays,a∉c.warrs) :
    Context B D k r fuel stride G x parts A extent front τ := by
  exact frame_order rr hc ((rr.frame_var _ (hv _ (by simp [scalars]))).trans hc.order)
    (fun s hs _ => hv s hs) ha

/-- Full parent restoration from the concrete child-call/pop theorem
restores this context, including all source arrays and the recursion fuel.
Bounds and extents come from actual execution, rather than assumptions
about a child's scratch buffers. -/
theorem restored {n B D k r fuel stride steps total : ℕ}
    {cfg : Config} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → ℚ≥0} {parts : List (Finset (Fin n))} {A : Finset (Fin n)}
    {extent : String → ℕ} {front : List ℕ} {parent saved τ : Env}
    (hc : Context B D k r fuel stride G x parts A extent front saved)
    (trace : Segment B (phases cfg) steps total parent τ)
    (hparent : NativeStateBounds.Bounded B parent)
    (hlength : ∀ a,(parent.arrs a).length=extent a)
    (hv : ∀ s,s∉excludedScalars → τ.vars s=saved.vars s)
    (ha : ∀ a,a≠"recursion.frames" → τ.arrs a=saved.arrs a)
    (hfront : Prefix front "recursion.frames" τ) (hcursor : τ.vars "stack.words"=front.length) :
    Context B D k r fuel stride G x parts A extent front τ := by
  refine ⟨(hv _ (by decide)).trans hc.order,?_,?_,?_,
    (hv _ (by decide)).trans hc.count,(hv _ (by decide)).trans hc.denominator,
    (hv _ (by decide)).trans hc.target,(hv _ (by decide)).trans hc.dimension,?_,
    (hv _ (by decide)).trans hc.conditioning,NativeMachineBounds.state trace hparent,
    ?_,hfront,hcursor,(hv _ (by decide)).trans hc.width,(hv _ (by decide)).trans hc.depth⟩
  · simpa only [Prefix,ha "search.graph" (by decide)] using hc.graph
  · simpa only [Prefix,ha "near.costs" (by decide)] using hc.costs
  · simpa only [Prefix,ha "separator.pieces" (by decide)] using hc.pieces
  · simpa only [Prefix,ha "catalog.mask" (by decide)] using hc.catalog
  · intro a; rw [NativeMachineFrame.array_length trace]; exact hlength a

/-- Execute both actual light-part phases. The mathematical collector
returns the empty set, and every field needed for the next part is preserved. -/
theorem light_iteration (n D k r fuel stride h : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
    (parts : List (Finset (Fin n))) (A : Finset (Fin n))
    (extent : String → ℕ) (front : List ℕ)
    (hn : 0<n) (hD : 0<D) (hx : ∀ v,NativeSignedArithmetic.Bounded (2^h) (x v : ℚ))
    (w : ℕ) (hw : NativeComponentDecision.wordHeight n D k h≤w)
    (hparts : parts.length≤n+1) (i : ℕ) (hi : i<parts.length)
    (hB : i+parts.length+12<2^w)
    (hbits : n≤extent "subset.bits") (hlabels : n≤extent "restrict.vertices")
    (hlp : 3*n<extent "lp.word") (hsum : 3*n≤extent "sum.input")
    (light : ¬(1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈parts[i],(x v : ℚ)))
    (U : Finset (Fin n)) (σ : Env)
    (hin : NativeCollectionTrace.At (Context (2^w) D k r fuel stride G x parts A extent front) i U σ) :
    ∃ τ,Segment (2^w) (phases cfg) 2 (43*n+37+NativeComponentDecision.timeBound n h) σ τ ∧
      NativeCollectionTrace.At (Context (2^w) D k r fuel stride G x parts A extent front) (i+1) U τ ∧ NativeCollectionAnchor.Anchor σ τ := by
  let hc := hin.1
  obtain ⟨ν,load,hd,hm,hiν,ht,active,hr,hp⟩ :=
    NativeComponentTrace.load_segment n D k h cfg G x hn hD hx w hw parts hparts i hi hB σ
      ⟨hc.order,hc.graph,hc.costs,hin.2.1,hc.pieces,
        by rw [hc.lengths]; exact hbits,by rw [hc.lengths]; exact hlabels,
        hc.denominator,hc.target,by rw [hc.lengths]; exact hlp,by rw [hc.lengths]; exact hsum⟩
      hc.count hin.2.2.2.1 hin.2.2.2.2
  have runLoad := NativeMachineFrame.single_run load ⟨9,by change 9<16; decide⟩ hin.2.2.2.2
  change Run (2^w) component σ ν _ at runLoad
  have cν := frame runLoad hc (by decide) (by decide)
  have unionν : ν.vars "component.union"=mask U :=
    (runLoad.frame_var _ (by decide)).trans hin.2.2.1
  have active0 : ν.vars "component.active"=0 := by simpa only [if_neg light] using active
  obtain ⟨τ,advance,idx,running,phase⟩ := NativeComponentTrace.light_segment (2^w) i cfg (by omega) ν
    active0 hiν hr hp
  have runAdvance := NativeMachineFrame.single_run advance ⟨10,by change 10<16; decide⟩ hp
  change Run (2^w) (.ite (.eq (.var "component.active") (.lit 1)) (go 11)
    (NativeComponentControl.advance 9)) ν τ _ at runAdvance
  have totalEq : (43*n+27+NativeComponentDecision.timeBound n h)+10=
    43*n+37+NativeComponentDecision.timeBound n h := by omega
  refine ⟨τ,by simpa only [totalEq,Nat.reduceAdd] using NativeMachineSegment.append load advance,
    ⟨frame runAdvance cν (by decide) (by decide),idx,
      (runAdvance.frame_var _ (by decide)).trans unionν,running,phase⟩,
    NativeCollectionAnchor.frame (runLoad.seq runAdvance) (NativeCollectionAnchor.refl σ) (by decide) (by decide)⟩

/-- The two actual phases for a heavy part reach the recursive-call phase
with the parent's context, selected labels and target intact. -/
theorem heavy_entry (n D k r fuel stride h : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
    (parts : List (Finset (Fin n))) (A : Finset (Fin n))
    (extent : String → ℕ) (front : List ℕ)
    (hn : 0<n) (hD : 0<D) (hx : ∀ v,NativeSignedArithmetic.Bounded (2^h) (x v : ℚ))
    (w : ℕ) (hw : NativeComponentDecision.wordHeight n D k h≤w)
    (hparts : parts.length≤n+1) (i : ℕ) (hi : i<parts.length)
    (hB : i+parts.length+12<2^w)
    (hbits : n≤extent "subset.bits") (hlabels : n≤extent "restrict.vertices")
    (hlp : 3*n<extent "lp.word") (hsum : 3*n≤extent "sum.input")
    (heavy : (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈parts[i],(x v : ℚ)))
    (U : Finset (Fin n)) (σ : Env)
    (hin : NativeCollectionTrace.At (Context (2^w) D k r fuel stride G x parts A extent front) i U σ) :
    ∃ τ,Segment (2^w) (phases cfg) 2 (43*n+33+NativeComponentDecision.timeBound n h) σ τ ∧
      Context (2^w) D k r fuel stride G x parts A extent front τ ∧
      NativeRestrictionRead.Data G (fun v => (x v : ℚ)) parts[i] τ ∧
      τ.vars "component.mask"=mask parts[i] ∧ τ.vars "component.i"=i ∧
      τ.vars "component.union"=mask U ∧
      τ.vars "component.target"=ComputedRounding.target (1/(D : ℚ)) (∑ v∈parts[i],(x v : ℚ)) ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=11 ∧ NativeCollectionAnchor.Anchor σ τ := by
  let hc := hin.1
  obtain ⟨ν,load,hd,hm,hiν,ht,active,hr,hp⟩ :=
    NativeComponentTrace.load_segment n D k h cfg G x hn hD hx w hw parts hparts i hi hB σ
      ⟨hc.order,hc.graph,hc.costs,hin.2.1,hc.pieces,
        by rw [hc.lengths]; exact hbits,by rw [hc.lengths]; exact hlabels,
        hc.denominator,hc.target,by rw [hc.lengths]; exact hlp,by rw [hc.lengths]; exact hsum⟩
      hc.count hin.2.2.2.1 hin.2.2.2.2
  have runLoad := NativeMachineFrame.single_run load ⟨9,by change 9<16; decide⟩ hin.2.2.2.2
  change Run (2^w) component σ ν _ at runLoad
  have cν := frame runLoad hc (by decide) (by decide)
  have unionν : ν.vars "component.union"=mask U :=
    (runLoad.frame_var _ (by decide)).trans hin.2.2.1
  have active1 : ν.vars "component.active"=1 := by simpa only [if_pos heavy] using active
  obtain ⟨τ,advance,eqτ,running,phase⟩ := NativeComponentTrace.active_segment (2^w) cfg (by omega) ν
    active1 hr hp
  have runAdvance := NativeMachineFrame.single_run advance ⟨10,by change 10<16; decide⟩ hp
  change Run (2^w) (.ite (.eq (.var "component.active") (.lit 1)) (go 11)
    (NativeComponentControl.advance 9)) ν τ _ at runAdvance
  have totalEq : (43*n+27+NativeComponentDecision.timeBound n h)+6=
    43*n+33+NativeComponentDecision.timeBound n h := by omega
  refine ⟨τ,by simpa only [totalEq,Nat.reduceAdd] using NativeMachineSegment.append load advance,
    frame runAdvance cν (by decide) (by decide),?_,?_,?_,?_,?_,running,phase,
    NativeCollectionAnchor.frame (runLoad.seq runAdvance) (NativeCollectionAnchor.refl σ) (by decide) (by decide)⟩
  · exact NativeRestrictionRead.frame runAdvance hd (by decide) (by decide)
  · exact (runAdvance.frame_var _ (by decide)).trans hm
  · have rr : Run (2^w) (go 11) ν τ 2 := by
      subst τ
      exact Run.assign (evalB_lit (by omega : 11<2^w))
    exact (rr.frame_var _ (by decide)).trans hiν
  · exact (runAdvance.frame_var _ (by decide)).trans unionν
  · exact (runAdvance.frame_var _ (by decide)).trans ht

end Lax263307Proofs.NativeCollectionContext
