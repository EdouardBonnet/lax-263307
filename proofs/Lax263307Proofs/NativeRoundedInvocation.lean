import Lax263307Proofs.NativeRawOracle
import Lax263307Proofs.NativeRoundedStep

set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeRoundedInvocation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RoundedOracleSearch
open Matrix

/-- The checked rounded update can be invoked inside a larger native
program. Its numeric precision index is included in the actual time
budget, rather than incorrectly charged only by its bit size. -/
theorem exists_invocation : ∃ (p : Lax808846.Ram.Program) (c : ℕ),0<c ∧
    ∀ (n k h : ℕ),2≤n → 1≤h →
    ∀ (state : State n) (a : Fin n → ℤ),
    (∀ i j,Lax263307.NativeRoundedStep.height (state.1 i j) h) →
    (∀ i,Lax263307.NativeRoundedStep.height (rationalNormal a i) h) →
    (∀ i,Lax263307.NativeRoundedStep.height (state.2 i) h) →
    0<rationalNormal a ⬝ᵥ (state.1 *ᵥ rationalNormal a) →
    ∀ (B v : ℕ),c*(n+h+k+1)^12≤v →
    let T := c*(n+h+k+1)^12
    let xs := Lax263307.NativeRoundedStep.encodeInput k state a
    2*(2^v)^2+3<B → T+1<B → RamVirtualConstants.allowance p<B → xs.length+2<B →
    (∀ z∈xs,z<B) →
    Spec B (fun σ => Prefix xs "lp.word" σ ∧ σ.vars "lp.position"=xs.length ∧
      σ.vars "vm.width"=v ∧ xs.length≤(σ.arrs "vm.input").length ∧
      T<(σ.arrs "vm.addresses").length ∧ T<(σ.arrs "vm.values").length ∧ T<(σ.arrs "vm.output").length)
      (NativeRawOracle.command p)
      (fun _ τ => Prefix (Lax263307.NativeRoundedStep.encodeOutput (update k state a)) "vm.output" τ ∧
        τ.vars "vm.outputLength"=(Lax263307.NativeRoundedStep.encodeOutput (update k state a)).length ∧
        τ.vars "vm.running"=0) (NativeRawOracle.cost p xs.length T) := by
  obtain ⟨p,c,hc,hstep⟩ := NativeRoundedStep.exists_program
  refine ⟨p,c,hc,?_⟩
  intro n k h hn hh state a hA ha hcenter hpos B v hv
  dsimp only
  intro hB hT hp hlen hwords
  exact NativeRawOracle.command_spec B v (c*(n+h+k+1)^12) p _ _ hB hT hp hlen hwords
    (hstep n k h hn hh state a hA ha hcenter hpos v hv)

end Lax263307Proofs.NativeRoundedInvocation
