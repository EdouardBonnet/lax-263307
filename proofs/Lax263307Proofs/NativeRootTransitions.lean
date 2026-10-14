import Lax263307Proofs.NativeCoreMachine

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRootTransitions

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeCoreMachine Lax263307 NativeMasks

theorem frame_size_spec (B S : ℕ) (cfg : Config)
    (hB : S*(frameArrays cfg).length+(frameScalars cfg).length+S+(frameArrays cfg).length+10<B) :
    Spec B (fun σ => σ.vars "recursion.stride"=S) (frameSize cfg)
      (fun _ τ => τ.vars "frame.length"=S*(frameArrays cfg).length+(frameScalars cfg).length) 6 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem initialize_spec (B n fuel : ℕ) (hB : n+fuel+2<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "recursion.fuel"=fuel) initializeRoot
      (fun _ τ => τ.vars "root.target"=n ∧ τ.vars "root.fuel"=fuel ∧ τ.vars "stack.words"=0 ∧
        τ.vars "machine.running"=1 ∧ τ.vars "machine.phase"=0) 10 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]

theorem target_zero_spec (B : ℕ) (hB : 2<B) :
    Spec B (fun σ => σ.vars "root.target"=0) rootTarget
      (fun _ τ => τ.vars "root.mask"=0 ∧ τ.vars "root.value"=0 ∧ τ.vars "machine.running"=0) 10 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]

theorem target_positive_spec (B k fuel : ℕ) (hk : 0<k) (hB : k+fuel+2<B) :
    Spec B (fun σ => σ.vars "root.target"=k ∧ σ.vars "root.fuel"=fuel) rootTarget
      (fun σ τ => τ.vars "node.k"=k ∧ τ.vars "recursion.fuel"=fuel ∧ τ.vars "machine.phase"=1 ∧
        τ.vars "machine.running"=σ.vars "machine.running") 10 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem reply_none_spec (B k : ℕ) (hB : k+2<B) :
    Spec B (fun σ => σ.vars "recursion.return.tag"=0 ∧ σ.vars "root.target"=k+1) rootReply
      (fun σ τ => τ.vars "root.target"=k ∧ τ.vars "machine.phase"=0 ∧
        τ.vars "machine.running"=σ.vars "machine.running") 10 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem reply_some_spec {n : ℕ} (B k : ℕ) (I : Finset (Fin n)) (hB : k+2<B) (hm : 2^n<B) :
    Spec B (fun σ => NativeTargetDriver.Reply (some I) σ ∧ σ.vars "root.target"=k) rootReply
      (fun _ τ => τ.vars "root.mask"=mask I ∧ τ.vars "root.value"=k ∧ τ.vars "machine.running"=0) 10 := by
  have hmask : mask I<B := (mask_bound I).trans hm
  intro σ hs
  run_vcg
  all_goals simp_all [NativeTargetDriver.Reply,Env.setVar]
  all_goals omega

end Lax263307Proofs.NativeRootTransitions
