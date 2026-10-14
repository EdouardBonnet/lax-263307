import Lax263307Proofs.NativeFlowPrepare
import Lax263307Proofs.NativeFlowCut

namespace Lax263307Proofs.NativeSeparatorContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 NativeSignedArithmetic
open Lax109476.RationalEncoding
open scoped NNRat

def workspace : List String := ["restrict.vertices","subset.bits","lp.word","vm.input","vm.addresses","vm.values","vm.output","separator.cuts"]
def protectedVars : List String := ["graph.n","class.B","algorithm.load","conditioning.k"]

structure Context {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
    (b load k space : ℕ) (σ : Env) : Prop where
  graph : Prefix (NativeWeightReduction.adjacency G) "search.graph" σ
  costs : Prefix (encodeVector fun v => (x v : ℚ)) "near.costs" σ
  order : σ.vars "graph.n"=n
  classB : σ.vars "class.B"=b
  load : σ.vars "algorithm.load"=load
  target : σ.vars "conditioning.k"=k
  room : ∀ a∈workspace,space≤(σ.arrs a).length

theorem frame {B K n b load k space : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → ℚ≥0} {c : Com} {σ τ : Env} (rr : Run B c σ τ K) (hd : Context G x b load k space σ)
    (hv : ∀ s∈protectedVars,s∉c.wvars) (hg : "search.graph"∉c.warrs) (hx : "near.costs"∉c.warrs) :
    Context G x b load k space τ := by
  refine ⟨?_,?_,(rr.frame_var "graph.n" (hv _ (by simp [protectedVars]))).trans hd.order,
    (rr.frame_var "class.B" (hv _ (by simp [protectedVars]))).trans hd.classB,
    (rr.frame_var "algorithm.load" (hv _ (by simp [protectedVars]))).trans hd.load,
    (rr.frame_var "conditioning.k" (hv _ (by simp [protectedVars]))).trans hd.target,?_⟩
  · simpa only [Prefix,rr.frame_arr "search.graph" hg] using hd.graph
  · simpa only [Prefix,rr.frame_arr "near.costs" hx] using hd.costs
  · intro a ha; rw [RamFrames.run_array_length rr]; exact hd.room a ha

def callback (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq NativeFlowPrepare.command (NativeFlowCut.command p coeff)

theorem callback_variable (p : Lax808846.Ram.Program) (coeff : List ℕ) (s : String)
    (hp : s∉NativeFlowPrepare.command.wvars) (hi : s∉NativeSplitInput.command.wvars)
    (ho : s∉NativeOracleScalars.reserved) (hd : s∉NativeFlowCut.decodeCommand.wvars) :
    s∉(callback p coeff).wvars := by
  simpa only [callback,NativeFlowCut.command,NativeSplitOracle.command,Com.wvars,List.mem_append,not_or] using
    And.intro hp (And.intro (And.intro hi (NativeOracleScalars.command_variable p coeff s ho)) hd)

theorem callback_array (p : Lax808846.Ram.Program) (coeff : List ℕ) (s : String)
    (hp : s∉NativeFlowPrepare.command.warrs) (hi : s∉NativeSplitInput.command.warrs)
    (ho : s∉["vm.addresses","vm.values","vm.output","vm.input"]) (hd : s∉NativeFlowCut.decodeCommand.warrs) :
    s∉(callback p coeff).warrs := by
  simpa only [callback,NativeFlowCut.command,NativeSplitOracle.command,Com.warrs,List.mem_append,not_or] using
    And.intro hp (And.intro (And.intro hi (NativeOracleFrame.command_array p coeff s ho)) hd)

theorem callback_frame {B K n b load k space : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → ℚ≥0} {p : Lax808846.Ram.Program} {coeff : List ℕ} {σ τ : Env}
    (rr : Run B (callback p coeff) σ τ K) (hd : Context G x b load k space σ) :
    Context G x b load k space τ := by
  apply frame rr hd
  · intro s hs
    simp only [protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;>
      exact callback_variable p coeff _ (by decide) (by decide) (by decide) (by decide)
  · exact callback_array p coeff _ (by decide) (by decide) (by decide) (by decide)
  · exact callback_array p coeff _ (by decide) (by decide) (by decide) (by decide)

theorem set_var {n b load k space : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → ℚ≥0} {σ : Env} (hd : Context G x b load k space σ) (s : String) (v : ℕ)
    (hs : s∉protectedVars) : Context G x b load k space (σ.setVar s v) := by
  have hv : ∀ a∈protectedVars,(σ.setVar s v).vars a=σ.vars a := by
    intro a ha
    rw [vars_setVar]
    rw [if_neg (by intro he; subst a; exact hs ha)]
  exact ⟨hd.graph,hd.costs,(hv _ (by simp [protectedVars])).trans hd.order,
    (hv _ (by simp [protectedVars])).trans hd.classB,(hv _ (by simp [protectedVars])).trans hd.load,
    (hv _ (by simp [protectedVars])).trans hd.target,hd.room⟩

end Lax263307Proofs.NativeSeparatorContext
