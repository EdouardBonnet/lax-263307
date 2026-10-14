import Lax263307Proofs.NativeRoundTrace

namespace Lax263307Proofs.NativeRoundedTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment

def StoredState {n : ℕ} (k : ℕ) (state : State n) (σ : Env) : Prop :=
  Prefix (NativeRoundedQuery.shape state) "round.shape" σ ∧
    Prefix (NativeRoundedQuery.center state) "round.center" σ ∧
    σ.vars "vec.n"=n ∧ σ.vars "round.i"=k

/-- The concrete phase-13 invocation advances the stored trajectory and
realizes precisely the cut branch of the bounded-round outcome. Its call
specification is supplied by NativeRoundedControl.exists_program. -/
theorem update_segment {n m : ℕ} (B k limit cost : ℕ) (cfg : Config) (P : Env → Prop)
    (state : State n) (a : Fin n → ℤ)
    (call : Spec B P (NativeRoundedControl.command cfg.rounded 4 14)
      (fun _ τ => Prefix (NativeRoundedQuery.shape (update k state a)) "round.shape" τ ∧
        Prefix (NativeRoundedQuery.center (update k state a)) "round.center" τ ∧
        τ.vars "vec.n"=n ∧ NativeRoundedControl.Output m k limit 4 14 τ) cost)
    (σ : Env) (hi : P σ) (hr : σ.vars "machine.running"=1) (hp : σ.vars "machine.phase"=13) :
    ∃ τ,Segment B (phases cfg) 1 cost σ τ ∧ τ.vars "graph.n"=m ∧
      NativeRoundTrace.Outcome StoredState limit k state (.cut a : Reply n (Finset (Fin m))) τ := by
  obtain ⟨τ,rr,po⟩ := call σ hi
  have hrτ : τ.vars "machine.running"=1 := by
    apply (rr.frame_var _ ?_).trans hr
    simp only [NativeRoundedControl.command,Com.wvars,List.mem_append,not_or]
    refine ⟨by decide,NativeRoundedControl.update_variable cfg.rounded _
      (by decide) (by decide) (by decide) (by decide),?_⟩
    simp [NativeRoundedControl.finish,NativeAttemptReply.noneCommand,Com.wvars]
  have output := po.2.2.2
  dsimp only [NativeRoundedControl.Output] at output
  refine ⟨τ,NativeMachineSegment.phase hr ⟨13,by change 13<16; decide⟩ hp rr,output.1,
    ⟨po.1,po.2.1,po.2.2.1,output.2.1⟩,?_⟩
  by_cases hk : k+1<limit
  · simp only [hk,if_true]
    exact ⟨hrτ,by simpa only [hk,if_true] using output.2.2⟩
  · have hstop : NativeTargetDriver.Reply (none : Option (Finset (Fin m))) τ ∧
        τ.vars "machine.phase"=14 := by simpa only [hk,if_false] using output.2.2
    simp only [hk,if_false]
    exact ⟨hrτ,hstop.2,hstop.1⟩

end Lax263307Proofs.NativeRoundedTrace
