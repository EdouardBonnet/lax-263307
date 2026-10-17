import Lax263307.IndependentSetEncoding
import Lax263307Proofs.NativeMaskUnpack

namespace Lax263307Proofs.NativeCutTest

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open NativeMasks

def finish : Com := .ite (.lt (.mul (.lit 2) (.var "graph.n")) (.mul (.lit 3) (.var "unpack.card")))
  (.assign "separator.active" (.lit 1)) (.assign "separator.active" (.lit 0))

theorem finish_spec (B n r : ℕ) (hr : r≤n) (hB : 3*n+5<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "unpack.card"=r) finish
      (fun _ τ => τ.vars "separator.active"=(if 3*r≤2*n then 0 else 1)) 10 := by
  by_cases h : 3*r≤2*n
  all_goals simp only [h,if_true,if_false]
  all_goals run_vcg
  all_goals simp_all
  all_goals omega

def command : Com := .seq (.assign "unpack.mask" (.var "separator.remaining"))
  (.seq NativeMaskUnpack.command finish)

/-- The native continuation test compares exactly three times the
remaining cardinality with twice the original graph order. -/
theorem command_spec {n : ℕ} (B : ℕ) (R : Finset (Fin n)) (hB : 3*n+5<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "separator.remaining"=mask R ∧ n≤(σ.arrs "subset.bits").length)
      command (fun _ τ => τ.vars "separator.active"=(if 3*R.card≤2*n then 0 else 1) ∧
        Prefix (Lax263307.IndependentSetEncoding.encodeOutput R) "subset.bits" τ ∧ τ.vars "unpack.card"=R.card)
      (21*n+20) := by
  rintro σ ⟨hn,hR,hroom⟩
  let ν := σ.setVar "unpack.mask" (mask R)
  have r1 : Run B (.assign "unpack.mask" (.var "separator.remaining")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hR.symm,hR ▸ (mask_bound R).trans hm⟩)
  obtain ⟨μ,r2,p2⟩ := NativeMaskUnpack.command_spec B R (by omega) hm ν
    ⟨by simpa [ν] using hn,by simp [ν],hroom⟩
  obtain ⟨τ,r3,p3⟩ := finish_spec B n R.card (NativeMaskUnpack.card_bound R) hB μ
    ⟨((r1.seq r2).frame_var "graph.n" (by decide)).trans hn,p2.2⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),p3,
    by simpa only [Prefix,r3.frame_arr "subset.bits" (by decide)] using p2.1,
    (r3.frame_var "unpack.card" (by decide)).trans p2.2⟩

end Lax263307Proofs.NativeCutTest
