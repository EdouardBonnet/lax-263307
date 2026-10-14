import Lax263307Proofs.NativeFrameBuffers
import Lax263307Proofs.NativeBlockRestore

namespace Lax263307Proofs.NativeFrameBufferRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def command : List String → Com
  | [] => .skip
  | a::as => .seq (.seq (.assign "stack.copy.length" (.var "recursion.stride"))
      (NativeBlockRestore.command a)) (command as)

theorem array_frame (names : List String) (a : String) (ha : a∉names) : a∉(command names).warrs := by
  induction names with
  | nil => simp [command,Com.warrs]
  | cons b bs ih =>
    simp only [List.mem_cons,not_or] at ha
    simp [command,NativeBlockRestore.command,NativeBlockRestore.setup,NativeSlice.command,
      NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.warrs,ha.1,ih ha.2]

theorem prefix_left (front tail : List ℕ) (a : String) (σ : Env) (hp : Prefix (front++tail) a σ) :
    Prefix front a σ := by
  intro i hi
  have hx : i<(front++tail).length := by simp only [List.length_append]; omega
  have he : (front++tail)[i]'hx=front[i] := List.getElem_append_left hi
  simpa only [he] using hp i hx

theorem prefix_full (xs : List ℕ) (a : String) (σ : Env)
    (hp : Prefix xs a σ) (hlen : (σ.arrs a).length=xs.length) : σ.arrs a=xs := by
  apply List.ext_getElem
  · exact hlen
  · intro i hi hj
    have hh := hp i hj
    simpa only [List.getElem?_eq_getElem hi,Option.some.injEq] using hh

/-- Restore all saved working buffers exactly, including initialized
scratch cells. Previously stacked frames remain available and unchanged. -/
theorem command_spec (B S : ℕ) (names : List String) (front : List ℕ) (saved : Env)
    (hnames : names.Nodup) (hne : "recursion.frames"∉names)
    (hsaved : NativeStateBounds.Bounded B saved)
    (hext : ∀ a∈names,(saved.arrs a).length=S) (hB : front.length+S*names.length+2<B) :
    Spec B (fun σ => Prefix (front++NativeFrameBuffers.words names saved) "recursion.frames" σ ∧
      σ.vars "stack.read.i"=front.length ∧ σ.vars "recursion.stride"=S ∧
      ∀ a∈names,(σ.arrs a).length=S) (command names)
      (fun _ τ => Prefix (front++NativeFrameBuffers.words names saved) "recursion.frames" τ ∧
        (∀ a∈names,τ.arrs a=saved.arrs a) ∧ τ.vars "stack.read.i"=front.length+S*names.length)
      ((16*S+16)*names.length+1) := by
  induction names generalizing front with
  | nil =>
    rintro σ ⟨hp,hi,hs,he⟩
    exact ⟨σ,Run.skip,hp,by simp,by simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero] using hi⟩
  | cons a as ih =>
    have hnd := List.nodup_cons.mp hnames
    have ha : "recursion.frames"≠a := by intro h; apply hne; simp [h]
    have has : "recursion.frames"∉as := by intro h; exact hne (List.mem_cons_of_mem a h)
    let xs := saved.arrs a
    have hlen : xs.length=S := hext a (by simp)
    rintro σ ⟨hp,hi,hs,he⟩
    let ν := σ.setVar "stack.copy.length" S
    have hSB : S<B := by simp only [List.length_cons] at hB; nlinarith only [hB]
    have r1 : Run B (.assign "stack.copy.length" (.var "recursion.stride")) σ ν 2 := Run.assign
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hSB⟩)
    have hhead : Prefix (front++xs) "recursion.frames" ν := prefix_left (front++xs)
      (NativeFrameBuffers.words as saved) "recursion.frames" ν
      (by simpa only [Prefix,ν,arrs_setVar,NativeFrameBuffers.words,List.flatMap_cons,List.append_assoc] using hp)
    obtain ⟨μ,r2,p2⟩ := NativeBlockRestore.command_spec B a front xs ha
      (by rw [hlen]; simp only [List.length_cons] at hB; nlinarith only [hB])
      (fun z hz => hsaved.2.1 a z hz) ν
      ⟨hhead,by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hi,by simp [ν,hlen],
        by simpa only [ν,arrs_setVar,hlen] using (he a (by simp)).ge⟩
    have rr := r1.seq r2
    have harray : μ.arrs a=xs := prefix_full xs a μ p2.2.1
      (by rw [RamFrames.run_array_length rr,he a (by simp),hlen])
    have hstride := (rr.frame_var "recursion.stride" (by simp [NativeBlockRestore.command,NativeBlockRestore.setup,
      NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.wvars])).trans hs
    have hsource : Prefix ((front++xs)++NativeFrameBuffers.words as saved) "recursion.frames" μ := by
      simpa only [Prefix,rr.frame_arr "recursion.frames" (by simp [NativeBlockRestore.command,NativeBlockRestore.setup,
        NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.warrs,ha]),
        NativeFrameBuffers.words,List.flatMap_cons,List.append_assoc] using hp
    obtain ⟨τ,r3,p3⟩ := ih (front++xs) hnd.2 has (fun b hb => hext b (List.mem_cons_of_mem a hb))
      (by simp only [List.length_append,hlen,List.length_cons] at hB ⊢; nlinarith only [hB]) μ
      ⟨hsource,by simpa only [List.length_append] using p2.2.2,hstride,
        fun b hb => by rw [RamFrames.run_array_length rr]; exact he b (List.mem_cons_of_mem a hb)⟩
    refine ⟨τ,(rr.seq r3).mono ?_,?_,?_,?_⟩
    · rw [hlen]; simp only [List.length_cons]; nlinarith only []
    · simpa only [NativeFrameBuffers.words,List.flatMap_cons,List.append_assoc] using p3.1
    · intro b hb
      rcases List.mem_cons.mp hb with h | hb
      · rw [h]
        exact (r3.frame_arr a (array_frame as a hnd.1)).trans harray
      · exact p3.2.1 b hb
    · simp only [List.length_append,hlen,List.length_cons] at p3 ⊢
      nlinarith only [p3.2.2]

end Lax263307Proofs.NativeFrameBufferRestore
