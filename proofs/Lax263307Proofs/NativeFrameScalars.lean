import Lax263307Proofs.NativeStateBounds

namespace Lax263307Proofs.NativeFrameScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def words (names : List String) (σ : Env) : List ℕ := names.map σ.vars

def save : List String → Com
  | [] => .skip
  | s::ss => .seq (RamWordBuffer.append "recursion.frames" "stack.words" (.var s)) (save ss)

theorem save_variable (names : List String) (s : String) (hs : s≠"stack.words") : s∉(save names).wvars := by
  induction names with
  | nil => simp [save,Com.wvars]
  | cons t ts ih => simp [save,Com.wvars,RamWordBuffer.append,hs,ih]

/-- A fixed list of scalar names is saved by a fixed source program.
The saved values are the actual entry-state values, with no advice. -/
theorem save_spec (B : ℕ) (names : List String) (front : List ℕ)
    (hne : "stack.words"∉names) (hB : front.length+names.length+2<B) :
    Spec B (fun σ => NativeStateBounds.Bounded B σ ∧ Prefix front "recursion.frames" σ ∧
      σ.vars "stack.words"=front.length ∧ front.length+names.length≤(σ.arrs "recursion.frames").length)
      (save names) (fun σ τ => NativeStateBounds.Bounded B τ ∧
        Prefix (front++words names σ) "recursion.frames" τ ∧
        τ.vars "stack.words"=front.length+names.length) (7*names.length+1) := by
  induction names generalizing front with
  | nil =>
    rintro σ ⟨hd,hf,hp,hr⟩
    exact ⟨σ,Run.skip,hd,by simpa only [words,List.map_nil,List.append_nil] using hf,
      by simpa only [List.length_nil,Nat.add_zero] using hp⟩
  | cons s ss ih =>
    rintro σ ⟨hd,hf,hp,hr⟩
    have hs : s≠"stack.words" := by intro h; apply hne; simp [h]
    have hss : "stack.words"∉ss := by intro h; exact hne (List.mem_cons_of_mem s h)
    let v := σ.vars s
    obtain ⟨ν,r1,p1⟩ := RamWordBuffer.append_spec B "recursion.frames" "stack.words" front v (.var s)
      (by omega) (by simp only [List.length_cons] at hB; omega) σ
      ⟨hf,hp,by simp only [List.length_cons] at hr; omega,evalB_var (hd.1 s)⟩
    have r1' : Run B (RamWordBuffer.append "recursion.frames" "stack.words" (.var s)) σ ν 7 := r1
    have hd1 := NativeStateBounds.run r1' hd
    have hword : words ss ν=words ss σ := by
      apply List.map_congr_left
      intro t ht
      have htne : t≠"stack.words" := by intro h; exact hss (h ▸ ht)
      exact r1'.frame_var t (by simp [RamWordBuffer.append,Com.wvars,htne])
    have htB : (front++[v]).length+ss.length+2<B := by
      simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at hB ⊢
      omega
    have htroom : (front++[v]).length+ss.length≤(ν.arrs "recursion.frames").length := by
      rw [RamFrames.run_array_length r1']
      simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at hr ⊢
      omega
    obtain ⟨τ,r2,p2⟩ := ih (front++[v]) hss htB
      ν ⟨hd1,p1.1,by simpa only [List.length_append,List.length_singleton,List.length_nil] using p1.2,htroom⟩
    refine ⟨τ,(r1'.seq r2).mono (by simp only [List.length_cons]; omega),p2.1,?_,?_⟩
    · rw [hword] at p2
      simpa only [words,List.map_cons,List.append_assoc,List.singleton_append] using p2.2.1
    · simpa only [List.length_append,List.length_singleton,List.length_nil,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using p2.2.2

end Lax263307Proofs.NativeFrameScalars
