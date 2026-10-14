import Lax263307Proofs.NativeFlowShores

namespace Lax263307Proofs.NativeShoreOrientation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs
open Lax263307 ComputedSeparators NativeMasks

def countCommand (reg out : String) : Com := .seq (.assign "unpack.mask" (.var reg))
  (.seq NativeMaskUnpack.command (.assign out (.var "unpack.card")))

theorem count_spec {n : ℕ} (B : ℕ) (I : Finset (Fin n)) (reg out : String)
    (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars reg=mask I ∧ n≤(σ.arrs "subset.bits").length)
      (countCommand reg out) (fun _ τ => τ.vars out=I.card) (21*n+12) := by
  rintro σ ⟨hn,hI,hroom⟩
  let ν := σ.setVar "unpack.mask" (mask I)
  have r1 : Run B (.assign "unpack.mask" (.var reg)) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hI.symm,hI ▸ (mask_bound I).trans hm⟩)
  obtain ⟨μ,r2,p2⟩ := NativeMaskUnpack.command_spec B I hB hm ν
    ⟨by simpa [ν] using hn,by simp [ν],hroom⟩
  let τ := μ.setVar out I.card
  have r3 : Run B (.assign out (.var "unpack.card")) μ τ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨p2.2.symm,p2.2 ▸ (NativeMaskUnpack.card_bound I).trans_lt (by omega)⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),by simp [τ]⟩

def choose : Com := .ite (.lt (.var "shore.leftCard") (.var "shore.rightCard"))
  (.seq (.assign "cut.left" (.var "shore.right")) (.assign "cut.right" (.var "shore.left")))
  (.seq (.assign "cut.left" (.var "shore.left")) (.assign "cut.right" (.var "shore.right")))

theorem choose_spec {n : ℕ} (B : ℕ) (A C : Finset (Fin n)) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "shore.left"=mask A ∧ σ.vars "shore.right"=mask C ∧
      σ.vars "shore.leftCard"=A.card ∧ σ.vars "shore.rightCard"=C.card)
      choose (fun _ τ => τ.vars "cut.left"=mask (orient A C).1 ∧ τ.vars "cut.right"=mask (orient A C).2) 8 := by
  have hA := (mask_bound A).trans hm
  have hC := (mask_bound C).trans hm
  have hcA := NativeMaskUnpack.card_bound A
  have hcC := NativeMaskUnpack.card_bound C
  by_cases h : C.card≤A.card
  all_goals simp only [orient,h,if_true,if_false]
  all_goals run_vcg
  all_goals simp_all
  all_goals omega

def command : Com := .seq (countCommand "shore.left" "shore.leftCard")
  (.seq (countCommand "shore.right" "shore.rightCard") choose)

/-- Count the two lifted shores and apply exactly the same orientation
rule as the functional separator construction. -/
theorem command_spec {n : ℕ} (B : ℕ) (A C : Finset (Fin n)) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "shore.left"=mask A ∧ σ.vars "shore.right"=mask C ∧
      n≤(σ.arrs "subset.bits").length) command
      (fun _ τ => τ.vars "cut.left"=mask (orient A C).1 ∧ τ.vars "cut.right"=mask (orient A C).2) (42*n+32) := by
  rintro σ ⟨hn,hA,hC,hroom⟩
  obtain ⟨ν,r1,p1⟩ := count_spec B A "shore.left" "shore.leftCard" hB hm σ ⟨hn,hA,hroom⟩
  obtain ⟨μ,r2,p2⟩ := count_spec B C "shore.right" "shore.rightCard" hB hm ν
    ⟨(r1.frame_var "graph.n" (by decide)).trans hn,(r1.frame_var "shore.right" (by decide)).trans hC,
      by rwa [RamFrames.run_array_length r1]⟩
  obtain ⟨τ,r3,p3⟩ := choose_spec B A C hB hm μ
    ⟨((r1.seq r2).frame_var "shore.left" (by decide)).trans hA,
      ((r1.seq r2).frame_var "shore.right" (by decide)).trans hC,
      (r2.frame_var "shore.leftCard" (by decide)).trans p1,p2⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),p3⟩

end Lax263307Proofs.NativeShoreOrientation
