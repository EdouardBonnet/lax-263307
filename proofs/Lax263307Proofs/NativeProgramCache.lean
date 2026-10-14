import Lax263307Proofs.NativeSlice

namespace Lax263307Proofs.NativeProgramCache

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def copy (source target lengthVar : String) : Com :=
  .seq (.assign "fill.length" (.var lengthVar))
    (.seq (.assign "slice.start" (.lit 0)) (NativeSlice.command source target))

theorem copy_spec (B : ℕ) (source target lengthVar : String) (xs : List ℕ)
    (hne : source≠target) (hB : xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Prefix xs source σ ∧ σ.vars lengthVar=xs.length ∧ xs.length≤(σ.arrs target).length)
      (copy source target lengthVar)
      (fun _ τ => Prefix xs source τ ∧ Prefix xs target τ) (16*xs.length+10) := by
  rintro σ ⟨hp,hlen,hroom⟩
  let ν := σ.setVar "fill.length" xs.length
  have r1 : Run B (.assign "fill.length" (.var lengthVar)) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hlen.symm,hlen ▸ (by omega)⟩)
  let μ := ν.setVar "slice.start" 0
  have r2 : Run B (.assign "slice.start" (.lit 0)) ν μ 2 := Run.assign (evalB_lit (show 0<B by omega))
  obtain ⟨τ,r3,p3⟩ := NativeSlice.command_spec B source target [] xs [] hne (by simp; omega) hv μ
    ⟨⟨by simpa only [List.nil_append,List.append_nil,Prefix,(r1.seq r2).frame_arr source (by simp [Com.warrs])] using hp,
      by rfl⟩,by simp [μ,ν],by rw [RamFrames.run_array_length (r1.seq r2)]; exact hroom⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),
    by simpa only [NativeSlice.Context,List.nil_append,List.append_nil] using p3.1.1,p3.2⟩

def save : Com := .seq (.assign "node.programLength" (.var "lp.length"))
  (copy "lp.input" "moment.program" "lp.length")

def restore : Com := copy "moment.program" "lp.input" "node.programLength"

/-- Save the base moment LP before rounded initialization or an update
reuses the LP work buffer. The length is computed, not supplied as advice. -/
theorem save_spec (B : ℕ) (xs : List ℕ) (hB : xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Prefix xs "lp.input" σ ∧ σ.vars "lp.length"=xs.length ∧
      xs.length≤(σ.arrs "moment.program").length) save
      (fun _ τ => Prefix xs "moment.program" τ ∧ τ.vars "node.programLength"=xs.length)
      (16*xs.length+12) := by
  rintro σ ⟨hp,hlen,hroom⟩
  let ν := σ.setVar "node.programLength" xs.length
  have r1 : Run B (.assign "node.programLength" (.var "lp.length")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hlen.symm,hlen ▸ (by omega)⟩)
  obtain ⟨τ,r2,p2⟩ := copy_spec B "lp.input" "moment.program" "lp.length" xs (by decide) hB hv ν
    ⟨by simpa only [Prefix,ν,arrs_setVar] using hp,
      (r1.frame_var "lp.length" (by decide)).trans hlen,
      by rw [RamFrames.run_array_length r1]; exact hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.2,(r2.frame_var "node.programLength" (by decide)).trans (by rfl)⟩

/-- Restore the cached base LP at the start of a projection phase. -/
theorem restore_spec (B : ℕ) (xs : List ℕ) (hB : xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Prefix xs "moment.program" σ ∧ σ.vars "node.programLength"=xs.length ∧
      xs.length≤(σ.arrs "lp.input").length) restore
      (fun _ τ => Prefix xs "lp.input" τ ∧ Prefix xs "moment.program" τ ∧
        τ.vars "node.programLength"=xs.length) (16*xs.length+10) := by
  rintro σ ⟨hp,hlen,hroom⟩
  obtain ⟨τ,rr,p⟩ := copy_spec B "moment.program" "lp.input" "node.programLength" xs (by decide) hB hv σ
    ⟨hp,hlen,hroom⟩
  exact ⟨τ,rr,p.2,p.1,(rr.frame_var "node.programLength" (by decide)).trans hlen⟩

end Lax263307Proofs.NativeProgramCache
