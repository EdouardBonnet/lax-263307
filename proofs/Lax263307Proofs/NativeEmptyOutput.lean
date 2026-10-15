import Lax263307Proofs.NativeMasks
import Lax455465Proofs.RamEmitWords
import Lax62Proofs.Refine.Codegen.Harness

namespace Lax263307Proofs.NativeEmptyOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib Lax455465Proofs
open Lax263307 WeightedIndependentSet

def clear : Com := .seq (.assign "empty.i" (.lit 0))
  (.while (.lt (.var "empty.i") (.var "input.n")) (Fill.put "weighted.output" "empty.i" (.lit 0)))

def command : Com := .seq clear (.seq (.assign "emit.count" (.var "input.n"))
  (RamEmitWords.command "weighted.output" 1))

/-- The empty/all-nonpositive branch emits the complete original-order
membership vector, rather than an empty output tape. -/
theorem command_spec (B n : ℕ) (hB : n+3<B) :
    Spec B (fun σ => σ.vars "input.n"=n ∧ (σ.arrs "weighted.output").length=n)
      command (fun σ τ => τ.out=σ.out++encodeOutput (∅ : Finset (Fin n))) (24*n+14) := by
  have hfill := Fill.loop_spec B n "weighted.output" "empty.i" "input.n" (.lit 0) (fun _ => 0)
    (by decide) (by omega) (fun _ _ _ _ => evalB_lit (by omega : 0<B))
  rintro σ ⟨hn,hlen⟩
  have harray : ∃ g,σ.arrs "weighted.output"=arrOf n g := by
    refine ⟨fun i => (σ.arrs "weighted.output").getD i 0,?_⟩
    apply List.ext_getElem
    · simp [arrOf,hlen]
    · intro i hi hj
      simp only [arrOf,List.getElem_map,List.getElem_range]
      exact List.getElem_eq_getD 0
  obtain ⟨ν,r1,⟨g,hg,hzero⟩,hi⟩ := hfill σ ⟨harray,hn⟩
  have hnν : ν.vars "input.n"=n := (r1.frame_var _ (by simp [Fill.put,Com.wvars])).trans hn
  let μ := ν.setVar "emit.count" n
  have r2 : Run B (.assign "emit.count" (.var "input.n")) ν μ 2 := Run.assign (by
    rw [evalB_var_iff]; exact ⟨hnν.symm,hnν ▸ (by omega)⟩)
  have hp : RamEmitWords.Data "weighted.output" 1 (encodeOutput (∅ : Finset (Fin n))) μ := by
    intro i hii
    have hin : i<n := by simpa [encodeOutput] using hii
    simp only [μ,arrs_setVar,hg,arrOf,List.getElem?_ofFn,List.length_ofFn]
    simp [hin,hzero i hin,encodeOutput]
  obtain ⟨τ,r3,po⟩ := RamEmitWords.command_spec B "weighted.output" 1
    (encodeOutput (∅ : Finset (Fin n))) σ.out (by omega) (by omega)
    (by simp [encodeOutput]; omega) (by simp [encodeOutput]; omega)
    (by intro z hz; simp [encodeOutput,List.mem_ofFn] at hz; rcases hz with ⟨i,rfl⟩; omega) μ
    ⟨hp,by simp [μ,encodeOutput],by simpa [μ] using r1.out_eq (by simp [Fill.put,Com.NoWrite])⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by simp [Expr.size,encodeOutput]; omega),po⟩


end Lax263307Proofs.NativeEmptyOutput
