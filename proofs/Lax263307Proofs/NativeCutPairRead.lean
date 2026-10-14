import Lax263307Proofs.NativeCutRecords

namespace Lax263307Proofs.NativeCutPairRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 NativeMasks

theorem pair_getD {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) (i : ℕ) :
    (NativeCutRecords.words cs).getD (2*i) 0=mask (cs.getD i (∅,∅)).1 ∧
    (NativeCutRecords.words cs).getD (2*i+1) 0=mask (cs.getD i (∅,∅)).2 := by
  induction cs generalizing i with
  | nil => simp [NativeCutRecords.words,mask_empty]
  | cons s cs ih =>
    cases i with
    | zero => simp [NativeCutRecords.words]
    | succ i => simpa [NativeCutRecords.words,Nat.mul_succ,Nat.add_assoc] using ih i

def command : Com := .seq (.assign "piece.left" (.get "separator.cuts" (.mul (.lit 2) (.var "piece.i"))))
  (.seq (.assign "piece.right" (.get "separator.cuts" (.add (.mul (.lit 2) (.var "piece.i")) (.lit 1))))
    (.assign "fill.value" (.xor (.var "piece.right") (.and (.var "piece.right") (.var "piece.left")))))

/-- Read a recorded shore pair and compute the smaller side outside
its overlap with the retained shore. -/
theorem command_spec {n : ℕ} (B : ℕ) (cs : List (Finset (Fin n) × Finset (Fin n)))
    (i : ℕ) (hi : i<cs.length) (hB : 2*cs.length+4<B) (hm : 2^n<B) :
    Spec B (fun σ => Prefix (NativeCutRecords.words cs) "separator.cuts" σ ∧ σ.vars "piece.i"=i) command
      (fun _ τ => τ.vars "fill.value"=mask (cs[i].2\cs[i].1)) 18 := by
  have hlen := NativeCutRecords.length_words cs
  have h0 : 2*i<(NativeCutRecords.words cs).length := by omega
  have h1 : 2*i+1<(NativeCutRecords.words cs).length := by omega
  have he := pair_getD cs i
  simp only [List.getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem h0,List.getElem?_eq_getElem h1,
    Option.getD_some] at he
  rintro σ ⟨hp,hs⟩
  have hg0 := hp (2*i) h0
  have hg1 := hp (2*i+1) h1
  rw [he.1] at hg0
  rw [he.2] at hg1
  have hiB : i<B := by omega
  let ν := σ.setVar "piece.left" (mask cs[i].1)
  have r1 : Run B (.assign "piece.left" (.get "separator.cuts" (.mul (.lit 2) (.var "piece.i")))) σ ν 5 :=
    Run.assign (evalB_get (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hiB⟩) (by change 2*i<B; omega)) hg0 ((mask_bound _).trans hm))
  let μ := ν.setVar "piece.right" (mask cs[i].2)
  have hgν : (ν.arrs "separator.cuts")[2*i+1]?=some (mask cs[i].2) := hg1
  have r2 : Run B (.assign "piece.right" (.get "separator.cuts" (.add (.mul (.lit 2) (.var "piece.i")) (.lit 1)))) ν μ 7 :=
    Run.assign (evalB_get (evalB_bin (op:=.add) (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; simpa only [ν,vars_setVar,String.reduceEq,if_false] using And.intro hs.symm (hs ▸ hiB))
      (by change 2*i<B; omega)) (evalB_lit (by omega)) (by change 2*i+1<B; omega)) hgν ((mask_bound _).trans hm))
  have ht := mask_bound (cs[i].2\cs[i].1)
  have hinter := mask_bound (cs[i].2∩cs[i].1)
  have hlast : Spec B (fun σ => σ.vars "piece.left"=mask cs[i].1 ∧ σ.vars "piece.right"=mask cs[i].2)
      (.assign "fill.value" (.xor (.var "piece.right") (.and (.var "piece.right") (.var "piece.left"))))
      (fun _ τ => τ.vars "fill.value"=mask (cs[i].2\cs[i].1)) 6 := by
    have ha := (mask_bound cs[i].1).trans hm
    have hb := (mask_bound cs[i].2).trans hm
    have hc := hinter.trans hm
    have hd := ht.trans hm
    simp only [NativeSetMasks.inter,NativeSetMasks.sdiff] at hc hd ⊢
    run_vcg
    all_goals simp_all
  obtain ⟨τ,r3,p3⟩ := hlast μ ⟨by simp [μ,ν],by simp [μ]⟩
  exact ⟨τ,r1.seq (r2.seq r3),p3⟩

end Lax263307Proofs.NativeCutPairRead
