import Lax263307Proofs.NativeOracleCalls

namespace Lax263307Proofs.NativeOutputLength

open Lax455465Proofs
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

/-- The length of the answer of the chosen oracle is polynomially bounded
by its input size: every output word requires a write instruction. -/
theorem exists_bound (f : List ℕ → List ℕ) (hf : RamPolytime f) :
    ∃ P : Polynomial ℕ,∀ x : List ℕ,(f x).length≤P.eval (bitSize x) := by
  obtain ⟨p,wp,tp,hr⟩ := SparseRam.polynomial_execution f hf
  refine ⟨tp,?_⟩
  intro x
  obtain ⟨_,k,hk,s,hrun,_,hout,_⟩ := hr x
  have h := SparseBounds.run_output_le _ p k _ s hrun
  have hs : (f x).length≤k := by simpa only [hout,SparseRam.init,List.length_nil,Nat.zero_add] using h
  exact hs.trans hk

end Lax263307Proofs.NativeOutputLength
