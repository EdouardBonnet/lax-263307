import Lax263307Proofs.NativeRoundTrace

namespace Lax263307Proofs.NativeRoundedTrace

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch NativeCoreMachine NativeMachineSegment

def StoredState {n : ℕ} (k : ℕ) (state : State n) (σ : Env) : Prop :=
  Prefix (NativeRoundedQuery.shape state) "round.shape" σ ∧
    Prefix (NativeRoundedQuery.center state) "round.center" σ ∧
    σ.vars "vec.n"=n ∧ σ.vars "round.i"=k


end Lax263307Proofs.NativeRoundedTrace
