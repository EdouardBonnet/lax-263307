import Lax263307Proofs.NativeBlockAppend
import Lax263307Proofs.NativeStateBounds

namespace Lax263307Proofs.NativeFrameBuffers

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def words (names : List String) (σ : Env) : List ℕ := names.flatMap σ.arrs

theorem words_congr (names : List String) (σ τ : Env)
    (h : ∀ a∈names,σ.arrs a=τ.arrs a) : words names σ=words names τ := by
  induction names with
  | nil => rfl
  | cons a as ih =>
    have hi := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    change List.flatMap σ.arrs as=List.flatMap τ.arrs as at hi
    simp only [words,List.flatMap_cons]
    rw [h a (by simp),hi]

theorem words_length (names : List String) (S : ℕ) (σ : Env)
    (hS : ∀ a∈names,(σ.arrs a).length=S) : (words names σ).length=S*names.length := by
  induction names with
  | nil => simp [words]
  | cons a as ih =>
    have hi := ih (fun b hb => hS b (List.mem_cons_of_mem a hb))
    change (List.flatMap σ.arrs as).length=S*as.length at hi
    simp only [words,List.flatMap_cons,List.length_append,List.length_cons]
    rw [hS a (by simp),hi]
    nlinarith only []

def save : List String → Com
  | [] => .skip
  | a::as => .seq (.seq (.assign "stack.copy.length" (.var "recursion.stride"))
      (NativeBlockAppend.command a "recursion.frames")) (save as)

theorem array_frame (names : List String) (a : String) (ha : a≠"recursion.frames") : a∉(save names).warrs := by
  induction names with
  | nil => simp [save,Com.warrs]
  | cons b bs ih => simp [save,NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,Com.warrs,ha,ih]

theorem stride_frame (names : List String) : "recursion.stride"∉(save names).wvars := by
  induction names with
  | nil => simp [save,Com.wvars]
  | cons b bs ih => simp [save,NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,Com.wvars,ih]

/-- Save all working buffers in one recursion frame. The buffer list is
fixed in the source code, and the common stride is computed at the root. -/
theorem save_spec (B S : ℕ) (names : List String) (front : List ℕ)
    (hne : "recursion.frames"∉names) (hB : front.length+S*names.length+2<B) :
    Spec B (fun σ => NativeStateBounds.Bounded B σ ∧ Prefix front "recursion.frames" σ ∧
      σ.vars "stack.words"=front.length ∧ σ.vars "recursion.stride"=S ∧
      (∀ a∈names,(σ.arrs a).length=S) ∧
      front.length+S*names.length≤(σ.arrs "recursion.frames").length) (save names)
      (fun σ τ => NativeStateBounds.Bounded B τ ∧
        Prefix (front++words names σ) "recursion.frames" τ ∧
        τ.vars "stack.words"=front.length+S*names.length) ((16*S+8)*names.length+1) := by
  induction names generalizing front with
  | nil =>
    rintro σ ⟨hd,hf,hp,hs,he,hr⟩
    exact ⟨σ,Run.skip,hd,by simpa only [words,List.flatMap_nil,List.append_nil] using hf,
      by simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero] using hp⟩
  | cons a as ih =>
    rintro σ ⟨hd,hf,hp,hs,he,hr⟩
    have ha : a≠"recursion.frames" := by intro h; apply hne; simp [h]
    have has : "recursion.frames"∉as := by intro h; exact hne (List.mem_cons_of_mem a h)
    let xs := σ.arrs a
    have hlen : xs.length=S := he a (by simp)
    let ν := σ.setVar "stack.copy.length" S
    have r1 : Run B (.assign "stack.copy.length" (.var "recursion.stride")) σ ν 2 := Run.assign
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hd.1 _⟩)
    have hheadB : front.length+xs.length+2<B := by rw [hlen]; simp only [List.length_cons] at hB; nlinarith only [hB]
    obtain ⟨μ,r2,p2⟩ := NativeBlockAppend.command_spec B a "recursion.frames" front xs ha hheadB
      (fun z hz => hd.2.1 a z hz) ν
      ⟨by intro i hi; exact List.getElem?_eq_getElem hi,
        by simpa only [Prefix,ν,arrs_setVar] using hf,by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hp,
        by simp [ν,hlen],by simpa only [ν,arrs_setVar,hlen] using
          (show front.length+S≤(σ.arrs "recursion.frames").length by simp only [List.length_cons] at hr; nlinarith only [hr])⟩
    have rr := r1.seq r2
    have hd2 := NativeStateBounds.run rr hd
    have hwords : words as μ=words as σ := by
      apply words_congr
      intro b hb
      have hbne : b≠"recursion.frames" := by intro h; exact has (h ▸ hb)
      exact rr.frame_arr b (by simp [NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,Com.warrs,hbne])
    have hstride := (rr.frame_var "recursion.stride" (by simp [NativeBlockAppend.command,NativeBlockAppend.step,
      RamWordBuffer.append,Com.wvars])).trans hs
    have htB : (front++xs).length+S*as.length+2<B := by
      simp only [List.length_append,hlen,List.length_cons] at hB ⊢
      nlinarith only [hB]
    obtain ⟨τ,r3,p3⟩ := ih (front++xs) has htB μ
      ⟨hd2,p2.2.1,by simpa only [List.length_append] using p2.2.2,hstride,
        (fun b hb => by rw [RamFrames.run_array_length rr]; exact he b (List.mem_cons_of_mem a hb)),
        by rw [RamFrames.run_array_length rr]; simp only [List.length_append,hlen,List.length_cons] at hr ⊢; nlinarith only [hr]⟩
    refine ⟨τ,((r1.seq r2).seq r3).mono ?_,p3.1,?_,?_⟩
    · rw [hlen]; simp only [List.length_cons]; nlinarith only []
    · rw [hwords] at p3
      simpa only [words,List.flatMap_cons,List.append_assoc] using p3.2.1
    · simp only [List.length_append,hlen,List.length_cons] at p3 ⊢
      nlinarith only [p3.2.2]

end Lax263307Proofs.NativeFrameBuffers
