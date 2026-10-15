import Lax263307Proofs.NativeOracleContext

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeNearExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning HeavyRationalConditioning ComputedSeparators
open NativeCoreMachine NativeMachineSegment NativeOracleContext

/-- Numerical and allocation obligations for the complete near branch.
These are inequalities, not hypotheses that phases execute. -/
structure Bounds (n r D k p M h T fuel S w : ℕ) (cfg : Config)
    (extent : String → ℕ) (front : List ℕ) : Prop where
  positive : 0<n
  denominator : 0<D
  sparsity : 0<p
  height : 1≤M
  reply : n+19<2^w
  moment : 3*NativeCatalogMetadata.N n r+10<2^w
  search : 3*(n*n)+3*n+r+10<2^w
  masks : 2^n<2^w
  rational : 2*M^2+3<2^w
  quadratic : 2*(NativeQuadraticSum.height M n)^2+3<2^w
  test : NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
    M (NativeQuadraticSum.height M n)<2^w
  floor : NativeConditioningFloor.base n p+NativeConditioningFloor.base n p^r+n+p+r+10<2^w
  costHeight : M^2≤2^h
  component : NativeComponentDecision.wordHeight n D k h≤w
  collection : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length+n*n+2*n+
    2*(n+1)+T+fuel+3*NativeCatalogMetadata.N n r+80<2^w
  frameExtents : ∀ a∈frameArrays cfg,extent a=S
  stack : front.length+S*(frameArrays cfg).length+(frameScalars cfg).length≤extent "recursion.frames"
  child : n*n≤extent "child.graph"
  graph : n*n≤extent "search.graph"
  bits : n≤extent "subset.bits"
  labels : n≤extent "restrict.vertices"
  word : 3*n+3*(n*n)<extent "lp.word"
  copy : 3*n≤extent "cut.source"
  sum : 3*(n*n)≤extent "sum.input"
  moments : 3*NativeCatalogMetadata.N n r≤extent "near.moments"
  costs : 3*n≤extent "near.costs"
  input : 3*NativeCatalogMetadata.N n r≤extent "lp.input"
  normal : 3*NativeCatalogMetadata.N n r≤extent "round.normal"
  pieces : n+1≤extent "separator.pieces"

def run {n r : ℕ} (flow : List ℕ → List ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D k p b load : ℕ) (y : RationalVector n r)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) : NearOracle.Result n :=
  match findHeavyConditioning G k p y with
  | none => .reject
  | some A =>
    let x := NearOracle.costs y A
    let cs := cuts (step flow G x b load k) n Finset.univ
    match ComputedRounding.collect (NearOracle.order cs.length) (pieces cs) (1/(D : ℚ)) k
      (fun i => ∑ v∈pieces cs i,(x v : ℚ))
      (fun i t => (child (pieces cs i) t).map (fun I => I.image (label (pieces cs i)))) with
    | .found I => .found I
    | .cut C u => .cut A C u

def Output {n : ℕ} (r : ℕ) : NearOracle.Result n → Env → Prop
  | .reject,σ => NativeRoundTrace.Stopped (none : Option (Finset (Fin n))) σ
  | .found I,σ => NativeRoundTrace.Stopped (some I) σ
  | .cut A C u,σ => σ.vars "machine.running"=1 ∧ σ.vars "machine.phase"=13 ∧
      NativeCollectionExecution.Cut r A C u σ

def timeBound (cfg : Config) (n r M S h childTime flowTime : ℕ) : ℕ :=
  (48*NativeCatalogMetadata.N n r+NativeHeavySearch.cost M n r+14)+10+
  ((17*NativeCatalogMetadata.N n r+72*(M^2).size+270)*n+17*NativeCatalogMetadata.N n r+67)+
  (flowTime+10)+NativeCollectionExecution.partCost cfg n r S h childTime*(n+1)+10

theorem stored_frame {B N j t : ℕ} {state : RoundedOracleSearch.State N}
    {σ τ : Env} {c : Com} (rr : Run B c σ τ t)
    (hs : NativeRoundedTrace.StoredState j state σ)
    (hv : "vec.n"∉c.wvars ∧ "round.i"∉c.wvars)
    (ha : "round.shape"∉c.warrs ∧ "round.center"∉c.warrs) :
    NativeRoundedTrace.StoredState j state τ := by
  refine ⟨?_,?_,(rr.frame_var _ hv.1).trans hs.2.2.1,(rr.frame_var _ hv.2).trans hs.2.2.2⟩
  · simpa only [Prefix,rr.frame_arr _ ha.1] using hs.1
  · simpa only [Prefix,rr.frame_arr _ ha.2] using hs.2.1

theorem separator_variable (cfg : Config) (s : String)
    (hf : s∉NativeFullSetMask.command.wvars)
    (ht : s∉NativeCutTest.command.wvars) (hr : s∉NativeCutRecords.command.wvars)
    (hi : s∉["separator.i","separator.count","separator.position","separator.value"])
    (hc : s∉(NativeSeparatorContext.callback cfg.flow cfg.flowWidth).wvars)
    (hp : s∉NativeCutPieces.command.wvars) (he : s∉(NativeComponentControl.start 9).wvars) :
    s∉((phases cfg)[8]'(by change 8<16; decide)).wvars := by
  simpa only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
    NativeCutLoop.step,NativeCutLoop.branch,Com.wvars,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false,not_or] using
    (show s∉(Com.seq (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
      (NativeComponentControl.start 9)).wvars from by
        simp only [NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
          NativeCutLoop.step,NativeCutLoop.branch,Com.wvars,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,not_or]
        simp_all)

theorem separator_array (cfg : Config) (s : String)
    (hf : s∉NativeFullSetMask.command.warrs)
    (ht : s∉NativeCutTest.command.warrs) (hr : s∉NativeCutRecords.command.warrs)
    (hc : s∉(NativeSeparatorContext.callback cfg.flow cfg.flowWidth).warrs)
    (hp : s∉NativeCutPieces.command.warrs) :
    s∉((phases cfg)[8]'(by change 8<16; decide)).warrs := by
  simp_all only [phases,cases,List.getElem_cons_succ,List.getElem_cons_zero,
    NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
    NativeCutLoop.step,NativeCutLoop.branch,NativeComponentControl.start,
    Com.warrs,List.mem_append,List.not_mem_nil,not_false_eq_true,not_or,and_true,true_and]

theorem separator_frame {n B D k r p b load F fuel S v limit t : ℕ} (cfg : Config)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent : String → ℕ} {front : List ℕ}
    {σ τ : Env} (rr : Run B ((phases cfg)[8]'(by change 8<16; decide)) σ τ t)
    (hc : Context B D k r p b load F fuel S v limit cfg G extent front σ) :
    Context B D k r p b load F fuel S v limit cfg G extent front τ := by
  apply NativeOracleContext.frame rr hc
  · intro s hs
    simp only [scalars,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply separator_variable <;> first | decide |
        exact NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)
  · intro s hs
    simp only [arrays,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply separator_array <;> first | decide |
        exact NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)

/-- Phases 6 through 12, including the entire collection and all nested
child executions, realize the functional near oracle. The only execution
premises are the selected flow solver's checked Spec and smaller-fuel
child execution. No whole-phase or collection execution is assumed. -/
theorem near_segment {n r : ℕ} (D k p b load F fuel S v limit M h T w space flowTime childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (flow : List ℕ → List ℕ) (x : Fin (NativeCatalogMetadata.N n r) → ℚ)
    (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card)))
    (bounds : Bounds n r D k p M h T fuel S w cfg extent front)
    (hx : ∀ i,NativeSignedArithmetic.Bounded M (x i))
    (hselected : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A → A.card≤r)
    (htarget : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A →
      ∀ C,ComputedRounding.target (1/(D : ℚ)) (∑ v∈C,(NearOracle.costs (MomentLP.decode x) A v : ℚ))≤T)
    (hspace : ∀ a∈NativeSeparatorContext.workspace,space≤extent a)
    (flowCall : ∀ A,let costs := NearOracle.costs (MomentLP.decode x) A
      let cs := cuts (step flow G costs b load k) n Finset.univ
      Spec (2^w) (fun σ => NativeSeparatorContext.Context G costs b load k space σ ∧
          n+1≤(σ.arrs "separator.pieces").length)
        (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
        (fun _ τ => NativeSeparatorContext.Context G costs b load k space τ ∧
          τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs) ∧
          τ.vars "separator.value"=NativeMasks.mask (separator cs) ∧ τ.vars "separator.count"=cs.length ∧
          Prefix (NativeCutRecords.words cs) "separator.cuts" τ ∧ τ.vars "separator.position"=2*cs.length ∧
          Prefix (NativeCutPieces.words cs) "separator.pieces" τ) flowTime)
    (recursive : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A →
      let costs := NearOracle.costs (MomentLP.decode x) A
      let cs := cuts (step flow G costs b load k) n Finset.univ
      ∀ i∈NearOracle.order cs.length,
      (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈pieces cs i,(costs v : ℚ)) → ∀ base σ,
      Protocol (2^w) D S v cfg extent front σ →
      NativeCollectionExecution.Invariant (2^w) D k r fuel S G costs
        ((NearOracle.order cs.length).map (pieces cs)) A extent front base σ →
      NativeRestrictionRead.Data G (fun v => (costs v : ℚ)) (pieces cs i) σ →
      σ.vars "component.mask"=NativeMasks.mask (pieces cs i) →
      σ.vars "component.target"=ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ)) →
      σ.vars "machine.running"=1 → σ.vars "machine.phase"=11 →
      NativeCollectionChild.Recursive (2^w) S fuel childSteps childTime cfg G (pieces cs i)
        (ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ))) front σ
        (child (pieces cs i) (ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ)))))
    (j : ℕ) (state : RoundedOracleSearch.State (NativeCatalogMetadata.N n r)) (σ : Env)
    (hc : Context (2^w) D k r p b load F fuel S v limit cfg G extent front σ)
    (hs : NativeRoundedTrace.StoredState j state σ)
    (hpoint : Prefix (encodeVector x) "lp.word" σ)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=6) :
    ∃ τ transitions total,Segment (2^w) (phases cfg) transitions total σ τ ∧
      transitions≤(childSteps+5)*(n+1)+4 ∧ total≤timeBound cfg n r M S h childTime flowTime ∧
      Context (2^w) D k r p b load F fuel S v limit cfg G extent front τ ∧
      NativeRoundedTrace.StoredState j state τ ∧
      Output r (run flow G D k p b load (MomentLP.decode x) child) τ ∧ RootData σ τ := by
  obtain ⟨ν,first,hrν,hpν,dataν,choiceν⟩ := NativeNearTrace.conditioning_segment
    (2^w) M n r k p cfg G x bounds.positive bounds.sparsity bounds.height bounds.moment
    bounds.search bounds.masks bounds.rational bounds.quadratic hx bounds.test bounds.floor σ
    hc.moments hpoint hc.target hc.sparsity
    (by rw [hc.lengths]; exact bounds.word) (by rw [hc.lengths]; exact bounds.copy)
    (by rw [hc.lengths]; exact bounds.sum) (by rw [hc.lengths]; exact bounds.moments) hr hp
  have r1 := NativeMachineFrame.single_run first ⟨6,by change 6<16; decide⟩ hp
  change Run (2^w) (.seq NativeMomentStorage.command (.seq NativeHeavySearch.command (go 7))) σ ν _ at r1
  have hcν := NativeOracleContext.frame r1 hc (by decide) (by decide)
  have hsν := stored_frame r1 hs (by decide) (by decide)
  cases choice : findHeavyConditioning G k p (MomentLP.decode x) with
  | none =>
    have choice0 : NativeHeavySearch.Output (none : Option (Finset (Fin n))) ν := by simpa [choice] using choiceν
    obtain ⟨τ,last,hout⟩ := NativeNearTrace.none_segment (2^w) n cfg bounds.reply ν hcν.moments.1.1 choice0 hrν hpν
    have r2 := NativeMachineFrame.single_run last ⟨7,by change 7<16; decide⟩ hpν
    change Run (2^w) conditioningReply ν τ _ at r2
    refine ⟨τ,2,_,NativeMachineSegment.append first last,by nlinarith,?_,
      NativeOracleContext.frame r2 hcν (by decide) (by decide),stored_frame r2 hsν (by decide) (by decide),?_,
      root_frame (r1.seq r2) (by decide) (by decide)⟩
    · dsimp only [timeBound]; omega
    · simpa only [run,choice,Output] using hout
  | some A =>
    have choiceA : NativeHeavySearch.Output (some A) ν := by simpa [choice] using choiceν
    have hA := hselected A choice
    let costs := NearOracle.costs (MomentLP.decode x) A
    let cs := cuts (step flow G costs b load k) n Finset.univ
    have hcs : cs.length≤n := NativeSeparatorOutput.cuts_length _ _ _
    obtain ⟨μ,second,hrμ,hpμ,dataμ,costsμ⟩ := NativeNearTrace.some_segment (2^w) M n r cfg G
      (MomentLP.decode x) A bounds.height hA bounds.moment (by have hh := bounds.search; omega) bounds.masks bounds.rational
      (fun T => hx ((CoordinateCatalog.indexing n r).symm T)) ν dataν choiceA
      (by rw [hcν.lengths]; have hh := bounds.word; omega) (by rw [hcν.lengths]; exact bounds.costs) hrν hpν
    have r2 := NativeMachineFrame.single_run second ⟨7,by change 7<16; decide⟩ hpν
    change Run (2^w) conditioningReply ν μ _ at r2
    have hcμ := NativeOracleContext.frame r2 hcν (by decide) (by decide)
    have hsμ := stored_frame r2 hsν (by decide) (by decide)
    have sepInput : NativeSeparatorContext.Context G costs b load k space μ :=
      ⟨hcμ.moments.1.2.2.2.1,costsμ,hcμ.moments.1.1,hcμ.classB,hcμ.loadValue,hcμ.target,
        fun a ha => by rw [hcμ.lengths]; exact hspace a ha⟩
    obtain ⟨ρ,third,sepρ,piecesρ,countρ,indexρ,unionρ,hrρ,hpρ⟩ := NativeSeparatorTrace.separator_segment
      (2^w) b load k space flowTime cfg G costs cs (flowCall A) (by have hh := bounds.reply; omega) μ sepInput
      (by rw [hcμ.lengths]; exact bounds.pieces) hrμ hpμ
    have r3 := NativeMachineFrame.single_run third ⟨8,by change 8<16; decide⟩ hpμ
    have hcρ := separator_frame cfg r3 hcμ
    have hsρ := stored_frame r3 hsμ
      ⟨separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
          (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide),
        separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
          (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)⟩
      ⟨separator_array cfg _ (by decide) (by decide) (by decide)
          (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide),
        separator_array cfg _ (by decide) (by decide) (by decide)
          (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)⟩
    have conditioningρ : ρ.vars "conditioning.choice"=NativeMasks.mask A := by
      apply (r3.frame_var _ (separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
        (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide))).trans
      exact (r2.frame_var _ (by decide)).trans choiceA.2
    have collectionInput : NativeCollectionContext.Context (2^w) D k r fuel S G costs
        ((NearOracle.order cs.length).map (pieces cs)) A extent front ρ := by
      refine ⟨hcρ.moments.1.1,hcρ.moments.1.2.2.2.1,sepρ.costs,?_,?_,hcρ.denominator,
        hcρ.target,hcρ.moments.1.2.1,hcρ.moments.1.2.2.1,conditioningρ,
        hcρ.bounded,hcρ.lengths,hcρ.stack,hcρ.cursor,hcρ.stride,hcρ.depth⟩
      · simpa only [List.map_map,Function.comp_def] using piecesρ
      · simpa [NearOracle.order] using countρ
    have hcost : ∀ v,NativeSignedArithmetic.Bounded (2^h) (costs v : ℚ) := by
      intro v
      have hh := NativeNearCosts.height M n r (MomentLP.decode x) A bounds.height hA
        (fun T => hx ((CoordinateCatalog.indexing n r).symm T)) v
      exact ⟨hh.1.trans bounds.costHeight,hh.2.trans bounds.costHeight⟩
    obtain ⟨τ,s,t,last,hsLast,htLast,out⟩ := NativeCollectionExecution.collect_segment
      D k r fuel S h T childSteps childTime cfg G costs (pieces cs) (NearOracle.order cs.length) A
      extent front ρ child (NativeCollectionSemantics.order_complete _) bounds.positive bounds.denominator
      hcost w bounds.component (by simp [NearOracle.order]; omega) bounds.masks
      (by have hb := bounds.collection; simp only [NearOracle.order,List.length_cons,List.length_map,List.length_finRange]; omega)
      (fun i _ => htarget A choice (pieces cs i)) bounds.frameExtents bounds.stack bounds.child bounds.graph
      bounds.bits bounds.labels (by have hh := bounds.word; omega) (by have hn := bounds.positive; have hh := bounds.sum; nlinarith)
      bounds.input bounds.normal
      (fun i hi heavy σ hσ hd hm ht hr hp => recursive A choice i hi heavy ρ σ
        (NativeOracleContext.collection_protocol hcρ hσ) hσ hd hm ht hr hp)
      ρ ⟨⟨collectionInput,NativeCollectionAnchor.refl ρ⟩,indexρ,by simpa [NativeMasks.mask,NativeCatalog.subsetMask] using unionρ,hrρ,hpρ⟩
    have hcτ := NativeOracleContext.collection hcρ last out.1.2 out.1.1.order out.1.1.stack out.1.1.cursor
    have hsτ := NativeCollectionAnchor.stored_state out.1.2 hsρ
    refine ⟨τ,_,_,NativeMachineSegment.append first (NativeMachineSegment.append second
        (NativeMachineSegment.append third last)),?_,?_,hcτ,hsτ,?_,?_⟩
    · simp only [NearOracle.order,List.length_cons,List.length_map,List.length_finRange] at hsLast
      nlinarith only [hsLast,hcs]
    · dsimp only [timeBound]
      have ht := Nat.mul_le_mul_left (NativeCollectionExecution.partCost cfg n r S h childTime)
        (Nat.add_le_add_right hcs 1)
      simp only [NearOracle.order,List.length_cons,List.length_map,List.length_finRange] at htLast
      omega
    · dsimp only [run]
      rw [choice]
      change Output r (match ComputedRounding.collect (NearOracle.order cs.length) (pieces cs) (1/(D : ℚ)) k
        (fun i => ∑ v∈pieces cs i,(costs v : ℚ))
        (fun i t => (child (pieces cs i) t).map (fun I => I.image (label (pieces cs i)))) with
        | .found I => .found I | .cut C u => .cut A C u) τ
      cases he : ComputedRounding.collect (NearOracle.order cs.length) (pieces cs) (1/(D : ℚ)) k
        (fun i => ∑ v∈pieces cs i,(costs v : ℚ))
        (fun i t => (child (pieces cs i) t).map (fun I => I.image (label (pieces cs i)))) <;>
        simpa only [NativeCollectionTrace.ResultOutput,he,Output] using out.2
    · apply RootData.trans (root_frame (r1.seq r2) (by decide) (by decide))
      apply RootData.trans (root_frame r3 ?_ ?_) (root_collection out.1.2)
      all_goals
        exact separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
          (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)

/-- All requirements consumed by the actual near execution theorem. The
recursive field refers only to smaller-fuel child execution. -/
structure Setup {n r : ℕ} (D k p b load fuel S v M h T w space flowTime childSteps childTime : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (flow : List ℕ → List ℕ) (x : Fin (NativeCatalogMetadata.N n r) → ℚ)
    (extent : String → ℕ) (front : List ℕ)
    (child : (C : Finset (Fin n)) → ℕ → Option (Finset (Fin C.card))) : Prop where
  bounds : Bounds n r D k p M h T fuel S w cfg extent front
  hx : ∀ i,NativeSignedArithmetic.Bounded M (x i)
  hselected : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A → A.card≤r
  htarget : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A →
      ∀ C,ComputedRounding.target (1/(D : ℚ)) (∑ v∈C,(NearOracle.costs (MomentLP.decode x) A v : ℚ))≤T
  hspace : ∀ a∈NativeSeparatorContext.workspace,space≤extent a
  flowCall : ∀ A,let costs := NearOracle.costs (MomentLP.decode x) A
      let cs := cuts (step flow G costs b load k) n Finset.univ
      Spec (2^w) (fun σ => NativeSeparatorContext.Context G costs b load k space σ ∧
          n+1≤(σ.arrs "separator.pieces").length)
        (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
        (fun _ τ => NativeSeparatorContext.Context G costs b load k space τ ∧
          τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs) ∧
          τ.vars "separator.value"=NativeMasks.mask (separator cs) ∧ τ.vars "separator.count"=cs.length ∧
          Prefix (NativeCutRecords.words cs) "separator.cuts" τ ∧ τ.vars "separator.position"=2*cs.length ∧
          Prefix (NativeCutPieces.words cs) "separator.pieces" τ) flowTime
  recursive : ∀ A,findHeavyConditioning G k p (MomentLP.decode x)=some A →
      let costs := NearOracle.costs (MomentLP.decode x) A
      let cs := cuts (step flow G costs b load k) n Finset.univ
      ∀ i∈NearOracle.order cs.length,
      (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈pieces cs i,(costs v : ℚ)) → ∀ base σ,
      Protocol (2^w) D S v cfg extent front σ →
      NativeCollectionExecution.Invariant (2^w) D k r fuel S G costs
        ((NearOracle.order cs.length).map (pieces cs)) A extent front base σ →
      NativeRestrictionRead.Data G (fun v => (costs v : ℚ)) (pieces cs i) σ →
      σ.vars "component.mask"=NativeMasks.mask (pieces cs i) →
      σ.vars "component.target"=ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ)) →
      σ.vars "machine.running"=1 → σ.vars "machine.phase"=11 →
      NativeCollectionChild.Recursive (2^w) S fuel childSteps childTime cfg G (pieces cs i)
        (ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ))) front σ
        (child (pieces cs i) (ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ))))

end Lax263307Proofs.NativeNearExecution
