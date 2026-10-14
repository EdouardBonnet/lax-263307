import Lax263307Proofs.NativeCutPairRead
import Lax263307Proofs.NativeTabulate

namespace Lax263307Proofs.NativeCutPieces

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def words {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) : List ℕ :=
  mask (remaining Finset.univ cs)::cs.map (fun s => mask (s.2\s.1))

structure Data {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) (σ : Env) : Prop where
  cuts : Prefix (NativeCutRecords.words cs) "separator.cuts" σ
  count : σ.vars "separator.count"=cs.length
  remaining : σ.vars "separator.remaining"=mask (ComputedSeparators.remaining Finset.univ cs)

theorem frame {B K n : ℕ} {cs : List (Finset (Fin n) × Finset (Fin n))} {c : Com} {σ τ : Env}
    (rr : Run B c σ τ K) (hd : Data cs σ) (hc : "separator.cuts"∉c.warrs)
    (hn : "separator.count"∉c.wvars) (hr : "separator.remaining"∉c.wvars) : Data cs τ := by
  refine ⟨?_,(rr.frame_var _ hn).trans hd.count,(rr.frame_var _ hr).trans hd.remaining⟩
  simpa only [Prefix,rr.frame_arr "separator.cuts" hc] using hd.cuts

def read : Com := .ite (.eq (.var "fill.i") (.lit 0))
  (.assign "fill.value" (.var "separator.remaining"))
  (.seq (.assign "piece.i" (.sub (.var "fill.i") (.lit 1))) NativeCutPairRead.command)

theorem read_spec {n : ℕ} (B : ℕ) (cs : List (Finset (Fin n) × Finset (Fin n)))
    (i : ℕ) (hi : i<(words cs).length) (hB : 2*cs.length+5<B) (hm : 2^n<B) :
    Spec B (fun σ => Data cs σ ∧ σ.vars "fill.i"=i) read
      (fun _ τ => Data cs τ ∧ τ.vars "fill.value"=(words cs)[i]) 26 := by
  have hlen : (words cs).length=cs.length+1 := by simp [words]
  have hiB : i<B := by rw [hlen] at hi; omega
  rintro σ ⟨hd,hs⟩
  have hc : (Cond.eq (.var "fill.i") (.lit 0)).evalB B σ=some (decide (i=0)) :=
    evalB_condEq (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hiB⟩) (evalB_lit (by omega))
  by_cases h : i=0
  · cases h
    let τ := σ.setVar "fill.value" (mask (remaining Finset.univ cs))
    have rr : Run B (.assign "fill.value" (.var "separator.remaining")) σ τ 2 := Run.assign
      (by rw [evalB_var_iff]; exact ⟨hd.remaining.symm,hd.remaining ▸ (mask_bound _).trans hm⟩)
    have rb : Run B read σ τ 26 := (Run.ite_true (by simpa only [decide_true] using hc) rr).mono (by simp [Cond.size,Expr.size])
    exact ⟨τ,rb,frame rb hd (by decide) (by decide) (by decide),by simp [τ,words]⟩
  · let j := i-1
    have hj : j<cs.length := by rw [hlen] at hi; dsimp [j]; omega
    have hij : i=j+1 := by dsimp [j]; omega
    let ν := σ.setVar "piece.i" j
    have r1 : Run B (.assign "piece.i" (.sub (.var "fill.i") (.lit 1))) σ ν 4 := Run.assign
      (evalB_bin (op:=.sub) (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hiB⟩) (evalB_lit (by omega))
        (by change i-1<B; omega))
    obtain ⟨τ,r2,p2⟩ := NativeCutPairRead.command_spec B cs j hj (by omega) hm ν ⟨hd.cuts,by simp [ν]⟩
    have rb : Run B read σ τ 26 := (Run.ite_false (by simpa only [h,decide_false] using hc) (r1.seq r2)).mono
      (by simp [Cond.size,Expr.size])
    refine ⟨τ,rb,frame rb hd (by decide) (by decide) (by decide),?_⟩
    simpa only [hij,words,List.getElem_cons_succ,List.getElem_map] using p2

def command : Com := .seq (.assign "fill.length" (.add (.var "separator.count") (.lit 1)))
  (NativeTabulate.command "separator.pieces" read)

/-- Materialize all component masks in the order none, then the
recorded cut indices. This is the exact Option-indexed pieces family. -/
theorem command_spec {n : ℕ} (B : ℕ) (cs : List (Finset (Fin n) × Finset (Fin n)))
    (hB : 2*cs.length+5<B) (hm : 2^n<B) :
    Spec B (fun σ => Data cs σ ∧ cs.length+1≤(σ.arrs "separator.pieces").length) command
      (fun _ τ => Data cs τ ∧ Prefix (words cs) "separator.pieces" τ) (37*(cs.length+1)+10) := by
  have hlen : (words cs).length=cs.length+1 := by simp [words]
  have hword : ∀ x∈words cs,x<B := by
    intro x hx
    simp only [words,List.mem_cons,List.mem_map] at hx
    rcases hx with rfl | ⟨s,hs,rfl⟩ <;> exact (mask_bound _).trans hm
  have hv := NativeTabulate.command_spec B (words cs) "separator.pieces" (Data cs) read 26
    (by rw [hlen]; omega) hword (by decide) (by decide) (by decide)
    (by intro σ hd; exact ⟨hd.cuts,by simpa using hd.count,by simpa using hd.remaining⟩)
    (fun _ _ rr hd => frame rr hd (by decide) (by decide) (by decide))
    (fun i hi => read_spec B cs i hi hB hm)
  rintro σ ⟨hd,hroom⟩
  let ν := σ.setVar "fill.length" (cs.length+1)
  have r1 : Run B (.assign "fill.length" (.add (.var "separator.count") (.lit 1))) σ ν 4 := Run.assign
    (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hd.count.symm,hd.count ▸ (by omega : cs.length<B)⟩)
      (evalB_lit (by omega)) (by change cs.length+1<B; omega))
  obtain ⟨τ,r2,p2⟩ := hv ν ⟨frame r1 hd (by decide) (by decide) (by decide),by simpa only [hlen] using
    (show ν.vars "fill.length"=cs.length+1 by simp [ν]),by simpa only [hlen,ν,arrs_setVar] using hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hlen]; omega),p2⟩

theorem none_word {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) :
    (words cs).getD 0 0=mask (pieces cs none) := rfl

theorem some_word {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) (i : Fin cs.length) :
    (words cs).getD (i.val+1) 0=mask (pieces cs (some i)) := by
  simp [words,pieces,List.getD,List.getElem?_eq_getElem i.isLt]

end Lax263307Proofs.NativeCutPieces
