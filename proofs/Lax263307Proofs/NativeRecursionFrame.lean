import Lax263307Proofs.NativeFrameBuffers
import Lax263307Proofs.NativeFrameBufferRestore
import Lax263307Proofs.NativeFrameScalars
import Lax263307Proofs.NativeFrameRestore

namespace Lax263307Proofs.NativeRecursionFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def words (arrays scalars : List String) (σ : Env) : List ℕ :=
  NativeFrameBuffers.words arrays σ++NativeFrameScalars.words scalars σ

def save (arrays scalars : List String) : Com := .seq (NativeFrameBuffers.save arrays) (NativeFrameScalars.save scalars)
def restore (arrays scalars : List String) : Com := .seq (NativeFrameBufferRestore.command arrays) (NativeFrameRestore.command scalars)

theorem scalars_array (names : List String) (a : String) : a∉(NativeFrameRestore.command names).warrs := by
  induction names with
  | nil => simp [NativeFrameRestore.command,Com.warrs]
  | cons s ss ih => simp [NativeFrameRestore.command,NativeFrameRestore.step,Com.warrs,ih]

theorem buffers_variable (names : List String) (s : String)
    (hs : s∉["stack.i","stack.copy.length","stack.words"]) : s∉(NativeFrameBuffers.save names).wvars := by
  induction names with
  | nil => simp [NativeFrameBuffers.save,Com.wvars]
  | cons a as ih =>
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
    simp [NativeFrameBuffers.save,NativeBlockAppend.command,NativeBlockAppend.step,RamWordBuffer.append,
      Com.wvars,hs.1,hs.2.1,hs.2.2,ih]

theorem scalar_values (names : List String) (σ τ : Env)
    (h : NativeFrameScalars.words names τ=NativeFrameScalars.words names σ) :
    ∀ s∈names,τ.vars s=σ.vars s := by
  induction names with
  | nil => simp
  | cons a as ih =>
    simp only [NativeFrameScalars.words,List.map_cons,List.cons.injEq] at h
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact h.1
    · exact ih h.2 s hs

/-- Save a complete finite working state in a fixed frame format. The
buffer and scalar lists are fixed before the graph input is supplied. -/
theorem save_spec (B S : ℕ) (arrays scalars : List String) (front : List ℕ)
    (ha : "recursion.frames"∉arrays)
    (hv : ∀ s∈scalars,s∉["stack.i","stack.copy.length","stack.words"])
    (hB : front.length+S*arrays.length+scalars.length+2<B) :
    Spec B (fun σ => NativeStateBounds.Bounded B σ ∧ Prefix front "recursion.frames" σ ∧
      σ.vars "stack.words"=front.length ∧ σ.vars "recursion.stride"=S ∧
      (∀ a∈arrays,(σ.arrs a).length=S) ∧
      front.length+S*arrays.length+scalars.length≤(σ.arrs "recursion.frames").length)
      (save arrays scalars) (fun σ τ => NativeStateBounds.Bounded B τ ∧
        Prefix (front++words arrays scalars σ) "recursion.frames" τ ∧
        τ.vars "stack.words"=front.length+S*arrays.length+scalars.length)
      ((16*S+8)*arrays.length+7*scalars.length+2) := by
  rintro σ ⟨hd,hp,hi,hs,he,hr⟩
  obtain ⟨ν,r1,p1⟩ := NativeFrameBuffers.save_spec B S arrays front ha (by omega) σ
    ⟨hd,hp,hi,hs,he,by omega⟩
  have hlen := NativeFrameBuffers.words_length arrays S σ he
  have hword : NativeFrameScalars.words scalars ν=NativeFrameScalars.words scalars σ := by
    apply List.map_congr_left
    intro s hs
    exact r1.frame_var s (buffers_variable arrays s (hv s hs))
  have hn : "stack.words"∉scalars := by
    intro h
    exact hv "stack.words" h (by simp)
  obtain ⟨τ,r2,p2⟩ := NativeFrameScalars.save_spec B scalars (front++NativeFrameBuffers.words arrays σ)
    hn (by simp only [List.length_append,hlen]; omega) ν
    ⟨p1.1,p1.2.1,by simpa only [List.length_append,hlen] using p1.2.2,
      by rw [RamFrames.run_array_length r1]; simp only [List.length_append,hlen]; omega⟩
  refine ⟨τ,(r1.seq r2).mono (by omega),p2.1,?_,?_⟩
  · rw [hword] at p2
    simpa only [words,List.append_assoc] using p2.2.1
  · simpa only [List.length_append,hlen,Nat.add_assoc] using p2.2.2

/-- Restore every saved working buffer and scalar, after arbitrary child
work that preserved the stack. The return cursor identifies the frame end. -/
theorem restore_spec (B S : ℕ) (arrays scalars : List String) (front : List ℕ) (saved : Env)
    (ha : "recursion.frames"∉arrays) (harrays : arrays.Nodup) (hscalars : scalars.Nodup)
    (hv : "stack.read.i"∉scalars) (hsaved : NativeStateBounds.Bounded B saved)
    (hext : ∀ a∈arrays,(saved.arrs a).length=S)
    (hB : front.length+S*arrays.length+scalars.length+2<B) :
    Spec B (fun σ => Prefix (front++words arrays scalars saved) "recursion.frames" σ ∧
      σ.vars "stack.read.i"=front.length ∧ σ.vars "recursion.stride"=S ∧
      ∀ a∈arrays,(σ.arrs a).length=S) (restore arrays scalars)
      (fun _ τ => Prefix (front++words arrays scalars saved) "recursion.frames" τ ∧
        (∀ a∈arrays,τ.arrs a=saved.arrs a) ∧ (∀ s∈scalars,τ.vars s=saved.vars s) ∧
        τ.vars "stack.read.i"=front.length+S*arrays.length+scalars.length)
      ((16*S+16)*arrays.length+7*scalars.length+2) := by
  rintro σ ⟨hp,hi,hs,he⟩
  have hlen := NativeFrameBuffers.words_length arrays S saved hext
  have hvarslen : (NativeFrameScalars.words scalars saved).length=scalars.length := by simp [NativeFrameScalars.words]
  have hfront : Prefix (front++NativeFrameBuffers.words arrays saved) "recursion.frames" σ :=
    NativeFrameBufferRestore.prefix_left _ _ _ _ (by simpa only [words,List.append_assoc] using hp)
  obtain ⟨ν,r1,p1⟩ := NativeFrameBufferRestore.command_spec B S arrays front saved harrays ha hsaved hext (by omega)
    σ ⟨hfront,hi,hs,he⟩
  have hframes : "recursion.frames"∉(NativeFrameBufferRestore.command arrays).warrs :=
    NativeFrameBufferRestore.array_frame arrays _ ha
  obtain ⟨τ,r2,p2⟩ := NativeFrameRestore.command_spec B scalars (front++NativeFrameBuffers.words arrays saved)
    (NativeFrameScalars.words scalars saved) hscalars hv hvarslen
    (by simp only [List.length_append,hlen,hvarslen]; omega)
    (by intro z hz; obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hz; exact hsaved.1 s) ν
    ⟨by simpa only [words,List.append_assoc,Prefix,r1.frame_arr "recursion.frames" hframes] using hp,
      by simpa only [List.length_append,hlen] using p1.2.2⟩
  refine ⟨τ,(r1.seq r2).mono (by omega),?_,?_,scalar_values scalars saved τ p2.2.1,?_⟩
  · simpa only [words,List.append_assoc] using p2.1
  · intro a ha
    exact (r2.frame_arr a (scalars_array scalars a)).trans (p1.2.1 a ha)
  · simpa only [List.length_append,hlen,hvarslen,Nat.add_assoc] using p2.2.2

end Lax263307Proofs.NativeRecursionFrame
