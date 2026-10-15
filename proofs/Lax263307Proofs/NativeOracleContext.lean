import Lax263307Proofs.NativeCollectionExecution
import Lax263307Proofs.NativeNearTrace
import Lax263307Proofs.NativeSeparatorTrace
import Lax263307Proofs.NativeProjectionTrace

namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment

def RootData (base σ : Env) : Prop :=
  σ.vars "root.target"=base.vars "root.target" ∧ σ.vars "root.fuel"=base.vars "root.fuel"

theorem RootData.refl (σ : Env) : RootData σ σ := ⟨rfl,rfl⟩

theorem RootData.trans {σ ν τ : Env} (h1 : RootData σ ν) (h2 : RootData ν τ) : RootData σ τ :=
  ⟨h2.1.trans h1.1,h2.2.trans h1.2⟩

theorem root_frame {B t : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ t)
    (ht : "root.target"∉c.wvars) (hf : "root.fuel"∉c.wvars) : RootData σ τ :=
  ⟨rr.frame_var _ ht,rr.frame_var _ hf⟩

theorem root_collection {σ τ : Env} (ha : NativeCollectionAnchor.Anchor σ τ) : RootData σ τ :=
  ⟨ha.1 _ (by decide),ha.1 _ (by decide)⟩

/-- The node-independent workspace and stack protocol. It is inherited by
an activated child and recovered when that child returns. -/
structure Protocol (B D S v : ℕ) (cfg : Config) (extent : String → ℕ)
    (front : List ℕ) (σ : Env) : Prop where
  bounded : NativeStateBounds.Bounded B σ
  lengths : ∀ a,(σ.arrs a).length=extent a
  stack : Prefix front "recursion.frames" σ
  cursor : σ.vars "stack.words"=front.length
  stride : σ.vars "recursion.stride"=S
  frameLength : σ.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length
  roundWidth : σ.vars "algorithm.roundWidth"=v
  accuracy : σ.vars "node.D"=D

/-- The fixed parent data shared by all branches of one oracle execution.
The evolving rounded state is kept separately. -/
structure Context {n : ℕ} (B D k r p b load F fuel S v limit : ℕ)
    (cfg : Config) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (extent : String → ℕ) (front : List ℕ) (σ : Env) : Prop where
  moments : NativeMomentAccess.Data G r σ
  target : σ.vars "conditioning.k"=k
  sparsity : σ.vars "conditioning.p"=p
  denominator : σ.vars "algorithm.D"=D
  classB : σ.vars "class.B"=b
  loadValue : σ.vars "algorithm.load"=load
  nodeD : σ.vars "node.D"=D
  floorPower : σ.vars "node.floorPower"=F
  program : Prefix (encodeProgram (MomentLP.program G k r)) "moment.program" σ
  programLength : σ.vars "node.programLength"=(encodeProgram (MomentLP.program G k r)).length
  roundLimit : σ.vars "round.limit"=limit
  roundWidth : σ.vars "algorithm.roundWidth"=v
  bounded : NativeStateBounds.Bounded B σ
  lengths : ∀ a,(σ.arrs a).length=extent a
  stack : Prefix front "recursion.frames" σ
  cursor : σ.vars "stack.words"=front.length
  stride : σ.vars "recursion.stride"=S
  depth : σ.vars "recursion.fuel"=fuel+1
  frameLength : σ.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length

theorem protocol {n B D k r p b load F fuel S v limit : ℕ} {cfg : Config}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent : String → ℕ} {front : List ℕ}
    {σ : Env} (hc : Context B D k r p b load F fuel S v limit cfg G extent front σ) :
    Protocol B D S v cfg extent front σ :=
  ⟨hc.bounded,hc.lengths,hc.stack,hc.cursor,hc.stride,hc.frameLength,hc.roundWidth,hc.nodeD⟩

/-- At every collection iteration the anchor preserves the fixed width,
frame size and accuracy; the collection context supplies the actual stack
and whole-state bounds. No execution hypothesis is needed for this use. -/
theorem collection_protocol {n B D k r p b load F fuel S v limit : ℕ} {cfg : Config}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent : String → ℕ} {front : List ℕ}
    {base σ : Env} {x : Fin n → ℚ≥0} {parts : List (Finset (Fin n))} {A : Finset (Fin n)}
    (hc : Context B D k r p b load F fuel S v limit cfg G extent front base)
    (hi : NativeCollectionExecution.Invariant B D k r fuel S G x parts A extent front base σ) :
    Protocol B D S v cfg extent front σ :=
  ⟨hi.1.bounded,hi.1.lengths,hi.1.stack,hi.1.cursor,hi.1.width,
    (hi.2.1 _ (by decide)).trans hc.frameLength,
    (hi.2.1 _ (by decide)).trans hc.roundWidth,(hi.2.1 _ (by decide)).trans hc.nodeD⟩

def scalars : List String := ["graph.n","catalog.count","moment.r",
  "conditioning.k","conditioning.p","algorithm.D","class.B","algorithm.load",
  "node.D","node.floorPower","node.programLength","round.limit","algorithm.roundWidth",
  "stack.words","recursion.stride","recursion.fuel","frame.length"]

def arrays : List String := ["catalog.mask","search.graph","catalog.card",
  "catalog.independent","moment.program","recursion.frames"]

theorem frame {n B D k r p b load F fuel S v limit t : ℕ} {cfg : Config}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent : String → ℕ} {front : List ℕ}
    {c : Com} {σ τ : Env} (rr : Run B c σ τ t)
    (hc : Context B D k r p b load F fuel S v limit cfg G extent front σ)
    (hv : ∀ s∈scalars,s∉c.wvars) (ha : ∀ a∈arrays,a∉c.warrs) :
    Context B D k r p b load F fuel S v limit cfg G extent front τ := by
  have v (s : String) (hs : s∈scalars) := rr.frame_var s (hv s hs)
  have a (s : String) (hs : s∈arrays) := rr.frame_arr s (ha s hs)
  refine ⟨?_,(v _ (by simp [scalars])).trans hc.target,
    (v _ (by simp [scalars])).trans hc.sparsity,
    (v _ (by simp [scalars])).trans hc.denominator,
    (v _ (by simp [scalars])).trans hc.classB,
    (v _ (by simp [scalars])).trans hc.loadValue,
    (v _ (by simp [scalars])).trans hc.nodeD,
    (v _ (by simp [scalars])).trans hc.floorPower,?_,
    (v _ (by simp [scalars])).trans hc.programLength,
    (v _ (by simp [scalars])).trans hc.roundLimit,
    (v _ (by simp [scalars])).trans hc.roundWidth,
    NativeStateBounds.run rr hc.bounded,?_,?_,
    (v _ (by simp [scalars])).trans hc.cursor,
    (v _ (by simp [scalars])).trans hc.stride,
    (v _ (by simp [scalars])).trans hc.depth,
    (v _ (by simp [scalars])).trans hc.frameLength⟩
  · refine ⟨NativeCatalogMetadata.data_frame G r rr (hv _ (by simp [scalars]))
      (hv _ (by simp [scalars])) (ha _ (by simp [arrays])) (ha _ (by simp [arrays])) hc.moments.1,
      ?_,?_,(v _ (by simp [scalars])).trans hc.moments.2.2.2⟩
    · simpa only [Prefix,a "catalog.card" (by simp [arrays])] using hc.moments.2.1
    · simpa only [Prefix,a "catalog.independent" (by simp [arrays])] using hc.moments.2.2.1
  · simpa only [Prefix,a "moment.program" (by simp [arrays])] using hc.program
  · intro s; rw [RamFrames.run_array_length rr]; exact hc.lengths s
  · simpa only [Prefix,a "recursion.frames" (by simp [arrays])] using hc.stack

/-- The collection anchor restores this context after arbitrary recursive
children; boundedness and exact extents follow from the actual trace. -/
theorem collection {n B D k r p b load F fuel S v limit steps total : ℕ} {cfg : Config}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {extent : String → ℕ} {front : List ℕ}
    {base τ : Env} (hc : Context B D k r p b load F fuel S v limit cfg G extent front base)
    (trace : Segment B (phases cfg) steps total base τ)
    (anchor : NativeCollectionAnchor.Anchor base τ)
    (order : τ.vars "graph.n"=n)
    (stack : Prefix front "recursion.frames" τ) (cursor : τ.vars "stack.words"=front.length) :
    Context B D k r p b load F fuel S v limit cfg G extent front τ := by
  have v (s : String) (hs : s∉NativeCollectionAnchor.workScalars) := anchor.1 s hs
  have a (s : String) (hs : s∉NativeCollectionAnchor.workArrays) := anchor.2 s hs
  refine ⟨?_,(v _ (by decide)).trans hc.target,(v _ (by decide)).trans hc.sparsity,
    (v _ (by decide)).trans hc.denominator,(v _ (by decide)).trans hc.classB,
    (v _ (by decide)).trans hc.loadValue,(v _ (by decide)).trans hc.nodeD,
    (v _ (by decide)).trans hc.floorPower,?_,(v _ (by decide)).trans hc.programLength,
    (v _ (by decide)).trans hc.roundLimit,(v _ (by decide)).trans hc.roundWidth,NativeMachineBounds.state trace hc.bounded,
    ?_,stack,cursor,(v _ (by decide)).trans hc.stride,(v _ (by decide)).trans hc.depth,
    (v _ (by decide)).trans hc.frameLength⟩
  · rcases hc.moments with ⟨⟨hn,hN,hm,hg,hbits⟩,hcard,hind,hr⟩
    refine ⟨⟨order,(v _ (by decide)).trans hN,?_,?_,?_⟩,
      ?_,?_,(v _ (by decide)).trans hr⟩
    · simpa only [Prefix,a "catalog.mask" (by decide)] using hm
    · simpa only [Prefix,a "search.graph" (by decide)] using hg
    · rw [NativeMachineFrame.array_length trace]; exact hbits
    · simpa only [Prefix,a "catalog.card" (by decide)] using hcard
    · simpa only [Prefix,a "catalog.independent" (by decide)] using hind
  · simpa only [Prefix,a "moment.program" (by decide)] using hc.program
  · intro s; rw [NativeMachineFrame.array_length trace]; exact hc.lengths s

/-- The actual large-node initializer supplies every fixed oracle field
and the initial stored rounded state. Only the incoming stack/workspace
protocol is supplied by the node entry invariant. -/
theorem of_large {n : ℕ} (B D k fuel S v : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (extent : String → ℕ) (front : List ℕ)
    (σ : Env) (ho : NativeLargeNode.Output cfg.a cfg.K cfg.b D k G σ)
    (hb : NativeStateBounds.Bounded B σ) (he : ∀ a,(σ.arrs a).length=extent a)
    (hstack : Prefix front "recursion.frames" σ) (hcursor : σ.vars "stack.words"=front.length)
    (hstride : σ.vars "recursion.stride"=S) (hdepth : σ.vars "recursion.fuel"=fuel+1)
    (hwidth : σ.vars "algorithm.roundWidth"=v)
    (hframe : σ.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length) :
    Context B D k (AlgorithmParameters.level cfg.a cfg.K cfg.b n D)
      (AlgorithmParameters.sparsity cfg.a cfg.K cfg.b n D) cfg.b (AlgorithmParameters.load cfg.b n D)
      ((AlgorithmParameters.floorDenominator cfg.a cfg.K cfg.b n D)^
        (AlgorithmParameters.level cfg.a cfg.K cfg.b n D)) fuel S v
      (AlgorithmParameters.iterations cfg.a cfg.K cfg.b n D) cfg G extent front σ ∧
    NativeRoundedTrace.StoredState 0
      ((1,0) : RoundedOracleSearch.State (MomentLP.dimension n (AlgorithmParameters.level cfg.a cfg.K cfg.b n D))) σ := by
  have aliases := ho.1
  have precision := ho.2.2.2.2.1
  refine ⟨⟨ho.2.1.1,aliases.2.1,aliases.2.2.1,aliases.2.2.2.2.1,aliases.2.2.2.2.2,
    aliases.2.2.2.1,precision.1.2.1,precision.2.1,ho.2.2.1,?_,?_,hwidth,
    hb,he,hstack,hcursor,hstride,hdepth,hframe⟩,
    ho.2.2.2.2.2.1,ho.2.2.2.2.2.2.1,precision.2.2.2.2.2,ho.2.2.2.2.2.2.2⟩
  · simpa only [NativeMomentInput.input_length] using ho.2.2.2.1
  · simpa only [NativeNodePrecision.actual_iterations] using precision.2.2.2.2.1

end Lax263307Proofs.NativeOracleContext
