import Lax263307Proofs.NativeNodeParameters

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodeAliases

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters

def command (b : ℕ) : Com := .seq (.assign "row.k" (.var "node.k"))
  (.seq (.assign "conditioning.k" (.var "node.k"))
    (.seq (.assign "conditioning.p" (.var "node.sparsity"))
      (.seq (.assign "algorithm.load" (.var "node.load"))
        (.seq (.assign "algorithm.D" (.var "node.D")) (.assign "class.B" (.lit b))))))

def Output (a K b n D k : ℕ) (σ : Env) : Prop :=
  σ.vars "row.k"=k ∧ σ.vars "conditioning.k"=k ∧ σ.vars "conditioning.p"=sparsity a K b n D ∧
    σ.vars "algorithm.load"=load b n D ∧ σ.vars "algorithm.D"=D ∧ σ.vars "class.B"=b

/-- Load the computed node budgets into the scalar names expected by
the checked moment, conditioning, separator and component commands. -/
theorem command_spec (B a K b n D k : ℕ) (hB : NativeNodeParameters.guard a K b n D+k+b+5<B) :
    Spec B (fun σ => NativeNodeParameters.Data a K b n D σ ∧ σ.vars "node.k"=k) (command b)
      (fun _ τ => Output a K b n D k τ) 12 := by
  intro σ hs
  run_vcg
  all_goals simp_all [NativeNodeParameters.Data,NativeNodeParameters.Context,Output,Env.setVar]
  all_goals dsimp only [NativeNodeParameters.guard] at hB
  all_goals omega

end Lax263307Proofs.NativeNodeAliases
