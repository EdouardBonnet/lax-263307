import Lax263307Proofs.NativeSetMasks
import Lax263307Proofs.NativeFlowCut

namespace Lax263307Proofs.NativeCutRecords

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def words {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) : List ℕ :=
  cs.flatMap fun s => [mask s.1,mask s.2]

theorem length_words {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) :
    (words cs).length=2*cs.length := by
  induction cs with
  | nil => rfl
  | cons s cs ih => simp only [words,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *; omega

theorem words_snoc {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) (A C : Finset (Fin n)) :
    words (cs++[(A,C)])=(words cs++[mask A])++[mask C] := by
  simp [words,List.append_assoc]

theorem separator_snoc {n : ℕ} (cs : List (Finset (Fin n) × Finset (Fin n))) (A C : Finset (Fin n)) :
    separator (cs++[(A,C)])=separator cs∪(A∩C) := by
  induction cs with
  | nil => simp [separator]
  | cons s cs ih =>
    simpa only [List.cons_append,separator,List.foldr_cons,Finset.union_assoc] using
      congrArg (fun S => (s.1∩s.2)∪S) ih

def update : Com := .seq (.assign "separator.remaining"
  (.xor (.var "cut.left") (.and (.var "cut.left") (.var "cut.right"))))
  (.seq (.assign "separator.value" (.or (.var "separator.value") (.and (.var "cut.left") (.var "cut.right"))))
    (.assign "separator.count" (.add (.var "separator.count") (.lit 1))))

theorem update_spec {n : ℕ} (B k : ℕ) (A C S : Finset (Fin n)) (hB : k+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "cut.left"=mask A ∧ σ.vars "cut.right"=mask C ∧
      σ.vars "separator.value"=mask S ∧ σ.vars "separator.count"=k) update
      (fun _ τ => τ.vars "separator.remaining"=mask (A\C) ∧
        τ.vars "separator.value"=mask (S∪(A∩C)) ∧ τ.vars "separator.count"=k+1) 16 := by
  have ha := (mask_bound A).trans hm
  have hc := (mask_bound C).trans hm
  have hs := (mask_bound S).trans hm
  have hi := (mask_bound (A∩C)).trans hm
  have hd := (mask_bound (A\C)).trans hm
  have hu := (mask_bound (S∪(A∩C))).trans hm
  simp only [NativeSetMasks.sdiff,NativeSetMasks.union,NativeSetMasks.inter] at hi hd hu ⊢
  run_vcg
  all_goals simp_all
  all_goals omega

def command : Com := .seq (RamWordBuffer.append "separator.cuts" "separator.position" (.var "cut.left"))
  (.seq (RamWordBuffer.append "separator.cuts" "separator.position" (.var "cut.right")) update)

/-- Append the actual ordered shore pair, accumulate its separator,
and retain the larger side outside the separator for the next cut. -/
theorem command_spec {n : ℕ} (B : ℕ) (cs : List (Finset (Fin n) × Finset (Fin n)))
    (A C : Finset (Fin n)) (hB : 2*cs.length+4<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "cut.left"=mask A ∧ σ.vars "cut.right"=mask C ∧
      σ.vars "separator.value"=mask (separator cs) ∧ σ.vars "separator.count"=cs.length ∧
      Prefix (words cs) "separator.cuts" σ ∧ σ.vars "separator.position"=2*cs.length ∧
      2*cs.length+2≤(σ.arrs "separator.cuts").length) command
      (fun _ τ => τ.vars "separator.remaining"=mask (A\C) ∧
        τ.vars "separator.value"=mask (separator (cs++[(A,C)])) ∧ τ.vars "separator.count"=cs.length+1 ∧
        Prefix (words (cs++[(A,C)])) "separator.cuts" τ ∧ τ.vars "separator.position"=2*(cs.length+1)) 30 := by
  rintro σ ⟨ha,hc,hs,hn,hprefix,hpos,hroom⟩
  obtain ⟨ν,r1,p1⟩ := RamWordBuffer.append_spec B "separator.cuts" "separator.position" (words cs) (mask A)
    (.var "cut.left") (by omega) (by rw [length_words]; omega) σ
    ⟨hprefix,by simpa only [length_words] using hpos,by rw [length_words]; omega,
      by rw [evalB_var_iff]; exact ⟨ha.symm,ha ▸ (mask_bound A).trans hm⟩⟩
  have hcν : ν.vars "cut.right"=mask C := (r1.frame_var "cut.right" (by decide)).trans hc
  obtain ⟨μ,r2,p2⟩ := RamWordBuffer.append_spec B "separator.cuts" "separator.position" (words cs++[mask A]) (mask C)
    (.var "cut.right") (by omega) (by simp only [List.length_append,List.length_singleton,length_words]; omega) ν
    ⟨p1.1,by simpa only [List.length_append,List.length_singleton] using p1.2,
      by rw [RamFrames.run_array_length r1]; simp only [List.length_append,List.length_singleton,length_words]; omega,
      by rw [evalB_var_iff]; exact ⟨hcν.symm,hcν ▸ (mask_bound C).trans hm⟩⟩
  have rr12 := r1.seq r2
  obtain ⟨τ,r3,p3⟩ := update_spec B cs.length A C (separator cs) (by omega) hm μ
    ⟨(rr12.frame_var "cut.left" (by decide)).trans ha,(rr12.frame_var "cut.right" (by decide)).trans hc,
      (rr12.frame_var "separator.value" (by decide)).trans hs,(rr12.frame_var "separator.count" (by decide)).trans hn⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by decide),p3.1,?_,p3.2.2,?_,?_⟩
  · simpa only [separator_snoc] using p3.2.1
  · simpa only [words_snoc,Prefix,r3.frame_arr "separator.cuts" (by decide)] using p2.1
  · rw [r3.frame_var "separator.position" (by decide),p2.2,List.length_append,List.length_singleton,length_words]
    omega

end Lax263307Proofs.NativeCutRecords
