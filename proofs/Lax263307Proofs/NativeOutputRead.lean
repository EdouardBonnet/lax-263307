import Lax263307Proofs.NativeOracleScalars

namespace Lax263307Proofs.NativeOutputRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

def command : Com := .ite (.lt (.var "output.index") (.var "vm.outputLength"))
  (.assign "output.value" (.get "vm.output" (.var "output.index")))
  (.assign "output.value" (.lit 0))

/-- The functional cut decoder uses getD, so the native decoder also
supplies zero on a short output. No certificate-validity assumption is
needed for the exact decoding equality. -/
theorem command_spec (B : ℕ) (xs : List ℕ) (i : ℕ) (hB : xs.length+i+2<B)
    (hwords : ∀ x∈xs,x<B) :
    Spec B (fun σ => Prefix xs "vm.output" σ ∧ σ.vars "vm.outputLength"=xs.length ∧ σ.vars "output.index"=i)
      command (fun _ τ => τ.vars "output.value"=xs.getD i 0) 7 := by
  rintro σ ⟨hp,hlen,hi⟩
  have hc : (Cond.lt (.var "output.index") (.var "vm.outputLength")).evalB B σ=some (decide (i<xs.length)) :=
    evalB_condLt (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega : i<B)⟩)
      (by rw [evalB_var_iff]; exact ⟨hlen.symm,hlen ▸ (by omega : xs.length<B)⟩)
  by_cases h : i<xs.length
  · let τ := σ.setVar "output.value" xs[i]
    have rr : Run B (.assign "output.value" (.get "vm.output" (.var "output.index"))) σ τ 3 :=
      Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by omega : i<B)⟩)
        (hp i h) (hwords _ (List.getElem_mem h)))
    exact ⟨τ,Run.ite_true (by simpa only [h,decide_true] using hc) rr,by simp [τ,List.getD,List.getElem?_eq_getElem h]⟩
  · let τ := σ.setVar "output.value" 0
    have rr : Run B (.assign "output.value" (.lit 0)) σ τ 2 := Run.assign (evalB_lit (by omega))
    exact ⟨τ,(Run.ite_false (by simpa only [h,decide_false] using hc) rr).mono (by decide),
      by simp [τ,List.getD,List.getElem?_eq_none (Nat.le_of_not_gt h)]⟩

end Lax263307Proofs.NativeOutputRead
