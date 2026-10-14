import Lax263307Proofs.NativeFrameScalars

namespace Lax263307Proofs.NativeFrameRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def step (s : String) : Com := .seq (.assign s (.get "recursion.frames" (.var "stack.read.i")))
  (.assign "stack.read.i" (.add (.var "stack.read.i") (.lit 1)))

def command : List String → Com
  | [] => .skip
  | s::ss => .seq (step s) (command ss)

theorem variable_frame (names : List String) (s : String) (hs : s∉names) (hr : s≠"stack.read.i") :
    s∉(command names).wvars := by
  induction names with
  | nil => simp [command,Com.wvars]
  | cons t ts ih => simp only [List.mem_cons,not_or] at hs; simp [command,step,Com.wvars,hs.1,hr,ih hs.2]

/-- Restore the exact scalar values of a saved frame using a fixed list
of distinct names. Neither the stack words nor other variables change. -/
theorem command_spec (B : ℕ) (names : List String) (front xs : List ℕ)
    (hnames : names.Nodup) (hne : "stack.read.i"∉names) (hlen : xs.length=names.length)
    (hB : front.length+xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Prefix (front++xs) "recursion.frames" σ ∧ σ.vars "stack.read.i"=front.length)
      (command names) (fun _ τ => Prefix (front++xs) "recursion.frames" τ ∧
        NativeFrameScalars.words names τ=xs ∧ τ.vars "stack.read.i"=front.length+xs.length)
      (7*names.length+1) := by
  induction names generalizing front xs with
  | nil =>
    have hx : xs=[] := List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using hlen)
    subst xs
    rintro σ ⟨hp,hi⟩
    exact ⟨σ,Run.skip,hp,rfl,by simpa only [List.length_nil,Nat.add_zero] using hi⟩
  | cons s ss ih =>
    cases xs with
    | nil => simp at hlen
    | cons v vs =>
      have hnd := List.nodup_cons.mp hnames
      have hs : s≠"stack.read.i" := by intro h; apply hne; simp [h]
      have hss : "stack.read.i"∉ss := by intro h; exact hne (List.mem_cons_of_mem s h)
      have hvB : v<B := hv v (by simp)
      rintro σ ⟨hp,hi⟩
      have hg : (σ.arrs "recursion.frames")[front.length]?=some v := by
        have hh := hp front.length (by simp)
        simpa only [List.getElem_append_right (le_refl _),Nat.sub_self,List.getElem_cons_zero] using hh
      let ν := σ.setVar s v
      have r1 : Run B (.assign s (.get "recursion.frames" (.var "stack.read.i"))) σ ν 3 :=
        Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by simp only [List.length_cons] at hB; omega)⟩) hg hvB)
      have hiν : ν.vars "stack.read.i"=front.length := (r1.frame_var "stack.read.i" (by simp [Com.wvars,Ne.symm hs])).trans hi
      let μ := ν.setVar "stack.read.i" (front.length+1)
      have r2 : Run B (.assign "stack.read.i" (.add (.var "stack.read.i") (.lit 1))) ν μ 4 :=
        Run.assign (evalB_bin (op:=.add)
          (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ (by simp only [List.length_cons] at hB; omega)⟩)
          (evalB_lit (show 1<B by simp only [List.length_cons] at hB; omega))
          (by change front.length+1<B; simp only [List.length_cons] at hB; omega))
      have rr : Run B (step s) σ μ 7 := r1.seq r2
      obtain ⟨τ,r3,p3⟩ := ih (front++[v]) vs hnd.2 hss (by simp only [List.length_cons] at hlen; omega)
        (by simp only [List.length_append,List.length_singleton,List.length_cons,List.length_nil] at hB ⊢; omega)
        (fun z hz => hv z (List.mem_cons_of_mem v hz)) μ
        ⟨by simpa only [Prefix,rr.frame_arr "recursion.frames" (by simp [step,Com.warrs]),List.append_assoc,List.singleton_append] using hp,
          by simp [μ]⟩
      have hsτ : τ.vars s=v := (r3.frame_var s (variable_frame ss s hnd.1 hs)).trans
        ((r2.frame_var s (by simp [Com.wvars,hs])).trans (by simp [ν]))
      refine ⟨τ,(rr.seq r3).mono (by simp only [List.length_cons]; omega),?_,?_,?_⟩
      · simpa only [List.append_assoc,List.singleton_append] using p3.1
      · simpa only [NativeFrameScalars.words,List.map_cons,hsτ] using congrArg (List.cons v) p3.2.1
      · simpa only [List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.add_assoc,Nat.add_comm 1] using p3.2.2

end Lax263307Proofs.NativeFrameRestore
