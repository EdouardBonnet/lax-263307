import Lax263307Proofs.NativeRoundTrace
import Lax263307Proofs.NativeCollectionSemantics

namespace Lax263307Proofs.NativeSeparatorTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeCoreMachine NativeMachineSegment

theorem running_unwritten (p : Lax808846.Ram.Program) (coeff : List ℕ) :
    "machine.running"∉(NativeSeparatorOutput.command p coeff).wvars := by
  have hc := NativeSeparatorContext.callback_variable p coeff "machine.running"
    (by decide) (by decide) (by decide) (by decide)
  simp only [NativeSeparatorOutput.command,NativeSeparatorProgram.command,NativeCutLoop.command,
    NativeCutLoop.step,NativeCutLoop.branch,Com.wvars,List.mem_append,not_or]
  simp only [hc,and_true,true_and]
  decide

/-- Phase 8 executes the concrete separator program, retains its canonical
part order, and starts collection at index zero with an empty union.
The call premise is the existing NativeSeparatorOutput.exists_program spec. -/
theorem separator_segment {n : ℕ} (B b load k space callCost : ℕ) (cfg : Config)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
    (cs : List (Finset (Fin n) × Finset (Fin n)))
    (call : Spec B (fun σ => NativeSeparatorContext.Context G x b load k space σ ∧
        n+1≤(σ.arrs "separator.pieces").length)
      (NativeSeparatorOutput.command cfg.flow cfg.flowWidth)
      (fun _ τ => NativeSeparatorContext.Context G x b load k space τ ∧
        τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs) ∧
        τ.vars "separator.value"=NativeMasks.mask (separator cs) ∧ τ.vars "separator.count"=cs.length ∧
        Prefix (NativeCutRecords.words cs) "separator.cuts" τ ∧ τ.vars "separator.position"=2*cs.length ∧
        Prefix (NativeCutPieces.words cs) "separator.pieces" τ) callCost)
    (hB : cs.length+12<B) (σ : Env)
    (hd : NativeSeparatorContext.Context G x b load k space σ)
    (hroom : n+1≤(σ.arrs "separator.pieces").length)
    (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=8) :
    ∃ τ,Segment B (phases cfg) 1 (callCost+10) σ τ ∧
      NativeSeparatorContext.Context G x b load k space τ ∧
      Prefix ((NearOracle.order cs.length).map (fun i => NativeMasks.mask (pieces cs i))) "separator.pieces" τ ∧
      τ.vars "component.count"=cs.length+1 ∧ τ.vars "component.i"=0 ∧ τ.vars "component.union"=0 ∧
      τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=9 := by
  obtain ⟨ν,r1,p1⟩ := call σ ⟨hd,hroom⟩
  obtain ⟨τ,r2,p2⟩ := NativeComponentControl.start_spec B cs.length 9 hB ν p1.2.2.2.1
  refine ⟨τ,NativeMachineSegment.phase hr ⟨8,by change 8<16; decide⟩ hp (r1.seq r2),?_,?_,
    p2.1,p2.2.1,p2.2.2.1,?_,p2.2.2.2⟩
  · exact NativeSeparatorContext.frame r2 p1.1
      (by intro s hs; simp only [NativeSeparatorContext.protectedVars,List.mem_cons,List.not_mem_nil,or_false] at hs
          rcases hs with rfl|rfl|rfl|rfl <;> decide) (by decide) (by decide)
  · have he := NativeCollectionSemantics.piece_words cs
    simpa only [←he,Prefix,r2.frame_arr "separator.pieces" (by decide)] using p1.2.2.2.2.2.2
  · exact (r2.frame_var _ (by decide)).trans ((r1.frame_var _ (running_unwritten _ _)).trans hr)

end Lax263307Proofs.NativeSeparatorTrace
