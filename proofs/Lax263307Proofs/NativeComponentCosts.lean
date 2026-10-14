import Lax263307Proofs.NativeRestrictionRead
import Lax455465Proofs.RamVectorEncoding

namespace Lax263307Proofs.NativeComponentCosts

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 ComputedSeparators NativeSignedArithmetic NativeRestrictionRead

def read : Com := .seq (.assign "restrict.row" (.var "component.vertex")) costRead

theorem read_spec (B M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (i : Fin R.card) (hB : 3*n+10<B)
    (hM : M<B) (hx : ∀ v,Bounded M (x v)) :
    Spec B (fun σ => Data G x R σ ∧ σ.vars "component.vertex"=i.val) read
      (fun _ τ => Data G x R τ ∧ RamRational.FractionOutput (x (label R i)) τ) 26 := by
  have hr := NativeMaskUnpack.card_bound R
  have hiB : i.val<B := i.isLt.trans_le hr |>.trans (by omega)
  rintro σ ⟨hd,hi⟩
  let ν := σ.setVar "restrict.row" i.val
  have r1 : Run B (.assign "restrict.row" (.var "component.vertex")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩)
  obtain ⟨τ,r2,p2⟩ := cost_spec B M n G x R i hB hM hx ν
    ⟨frame r1 hd (by decide) (by decide),by simp [ν]⟩
  exact ⟨τ,r1.seq r2,p2⟩

def command : Com := .seq (.assign "lp.position" (.lit 0))
  (RamVectorEncoding.command "component.vertex" "restrict.count" read)

/-- Materialize the costs of the component vertices in the same canonical
order used by the recursive child graph. -/
theorem command_spec (B M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (hB : 3*n+10<B) (hM : M<B)
    (hx : ∀ v,Bounded M (x v)) :
    Spec B (fun σ => Data G x R σ ∧ 3*R.card<(σ.arrs "lp.word").length) command
      (fun _ τ => Data G x R τ ∧ Prefix (encodeVector (fun i => x (label R i))) "lp.word" τ ∧
        τ.vars "lp.position"=3*R.card) (61*R.card+8) := by
  let qs := List.ofFn (fun i : Fin R.card => x (label R i))
  have hr := NativeMaskUnpack.card_bound R
  have hv := RamVectorEncoding.command_spec B 26 (Data G x R) "component.vertex" "restrict.count" qs [] read
    (by omega) (by simp [qs]; omega)
    (by intro i hi; simp only [qs,List.getElem_ofFn]; exact (hx _).1.trans_lt hM)
    (by intro i hi; simp only [qs,List.getElem_ofFn]; exact (hx _).2.trans_lt hM)
    (fun _ hd => by simpa only [qs,List.length_ofFn] using hd.count)
    (by
      intro σ k hd
      exact ⟨hd.labels,hd.graph,hd.costs,by simpa using hd.count,by simpa using hd.order⟩)
    (by
      intro i hi
      simpa only [qs,List.getElem_ofFn] using read_spec B M n G x R ⟨i,by simpa [qs] using hi⟩ hB hM hx)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr hd => frame rr hd (by decide) (by decide)) (by decide)
  rintro σ ⟨hd,hroom⟩
  let ν := σ.setVar "lp.position" 0
  have r1 : Run B (.assign "lp.position" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (show 0<B by omega))
  obtain ⟨τ,r2,p2⟩ := hv ν ⟨frame r1 hd (by decide) (by decide),by simp [Prefix],by simp [ν],
    by simpa only [List.length_nil,qs,List.length_ofFn,Nat.zero_add,ν,arrs_setVar] using hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by simp only [qs,List.length_ofFn]; omega),p2.1,
    by simpa only [List.nil_append,RamVectorEncoding.encode,qs,encodeVector] using p2.2.1,
    by simpa only [List.length_nil,qs,List.length_ofFn,Nat.zero_add] using p2.2.2⟩

end Lax263307Proofs.NativeComponentCosts
