import Lax263307Proofs.NativeRecursionFrame

namespace Lax263307Proofs.NativeStackReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def bufferScratch : List String :=
  ["stack.copy.length","fill.length","slice.start","fill.value","fill.i","stack.read.i"]

theorem buffers_variable (arrays : List String) (s : String) (hs : s∉bufferScratch) :
    s∉(NativeFrameBufferRestore.command arrays).wvars := by
  simp only [bufferScratch,List.mem_cons,List.not_mem_nil,or_false,not_or] at hs
  induction arrays with
  | nil => simp [NativeFrameBufferRestore.command,Com.wvars]
  | cons a as ih =>
    simp [NativeFrameBufferRestore.command,NativeBlockRestore.command,NativeBlockRestore.setup,
      NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,
      RamWordBuffer.append,Com.wvars,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2,ih]

theorem restore_variable (arrays scalars : List String) (s : String)
    (hs : s∉bufferScratch) (hn : s∉scalars) : s∉(NativeRecursionFrame.restore arrays scalars).wvars := by
  have hr : s≠"stack.read.i" := fun h => hs (by simp [bufferScratch,h])
  simpa only [NativeRecursionFrame.restore,Com.wvars,List.mem_append,not_or] using
    And.intro (buffers_variable arrays s hs) (NativeFrameRestore.variable_frame scalars s hn hr)

def setup : Com := .seq (.assign "stack.words" (.sub (.var "stack.words") (.var "frame.length")))
  (.assign "stack.read.i" (.var "stack.words"))

def pop (arrays scalars : List String) : Com := .seq setup (NativeRecursionFrame.restore arrays scalars)

/-- Pop one fixed-size frame and restore its parent continuation while
retaining the child's return tag and mask. Old bytes beyond the stack cursor
may remain in the frame buffer and are harmless. -/
theorem pop_spec (B S : ℕ) (arrays scalars : List String) (front : List ℕ) (saved : Env)
    (ha : "recursion.frames"∉arrays) (harrays : arrays.Nodup) (hscalars : scalars.Nodup)
    (hv : "stack.read.i"∉scalars) (hw : "stack.words"∉scalars)
    (htag : "recursion.return.tag"∉scalars) (hmask : "recursion.return.mask"∉scalars)
    (hsaved : NativeStateBounds.Bounded B saved)
    (hext : ∀ a∈arrays,(saved.arrs a).length=S)
    (hB : front.length+S*arrays.length+scalars.length+2<B) :
    Spec B (fun σ => Prefix (front++NativeRecursionFrame.words arrays scalars saved) "recursion.frames" σ ∧
      σ.vars "stack.words"=front.length+S*arrays.length+scalars.length ∧
      σ.vars "frame.length"=S*arrays.length+scalars.length ∧ σ.vars "recursion.stride"=S ∧
      ∀ a∈arrays,(σ.arrs a).length=S) (pop arrays scalars)
      (fun σ τ => Prefix front "recursion.frames" τ ∧
        (∀ a∈arrays,τ.arrs a=saved.arrs a) ∧ (∀ s∈scalars,τ.vars s=saved.vars s) ∧
        τ.vars "stack.words"=front.length ∧ τ.vars "recursion.return.tag"=σ.vars "recursion.return.tag" ∧
        τ.vars "recursion.return.mask"=σ.vars "recursion.return.mask")
      ((16*S+16)*arrays.length+7*scalars.length+8) := by
  rintro σ ⟨hp,hwords,hlen,hstride,he⟩
  let ν := σ.setVar "stack.words" front.length
  have r1 : Run B (.assign "stack.words" (.sub (.var "stack.words") (.var "frame.length"))) σ ν 4 := by
    apply Run.assign
    have ew : (Expr.var "stack.words").evalB B σ=some (front.length+S*arrays.length+scalars.length) := by
      rw [evalB_var_iff]
      exact ⟨hwords.symm,hwords ▸ (by omega)⟩
    have el : (Expr.var "frame.length").evalB B σ=some (S*arrays.length+scalars.length) := by
      rw [evalB_var_iff]
      exact ⟨hlen.symm,hlen ▸ (by omega)⟩
    have hh := evalB_bin (op:=.sub)
      ew el
      (by change front.length+S*arrays.length+scalars.length-(S*arrays.length+scalars.length)<B; omega)
    have heq : front.length+S*arrays.length+scalars.length-(S*arrays.length+scalars.length)=front.length := by omega
    simpa only [Bop.apply_sub,heq] using hh
  let μ := ν.setVar "stack.read.i" front.length
  have r2 : Run B (.assign "stack.read.i" (.var "stack.words")) ν μ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨by simp [ν],by simp [ν]; omega⟩)
  obtain ⟨τ,r3,p3⟩ := NativeRecursionFrame.restore_spec B S arrays scalars front saved ha harrays hscalars hv hsaved hext hB μ
    ⟨hp,by simp [μ],(r2.frame_var _ (by decide)).trans ((r1.frame_var _ (by decide)).trans hstride),
      by intro a ha; rw [RamFrames.run_array_length (r1.seq r2)]; exact he a ha⟩
  have rr := (r1.seq r2).seq r3
  refine ⟨τ,rr.mono (by omega),NativeFrameBufferRestore.prefix_left _ _ _ _ p3.1,p3.2.1,p3.2.2.1,?_,?_,?_⟩
  · exact (r3.frame_var _ (restore_variable arrays scalars _ (by decide) hw)).trans
      ((r2.frame_var _ (by decide)).trans (by simp [ν]))
  · exact (r3.frame_var _ (restore_variable arrays scalars _ (by decide) htag)).trans ((r1.seq r2).frame_var _ (by decide))
  · exact (r3.frame_var _ (restore_variable arrays scalars _ (by decide) hmask)).trans ((r1.seq r2).frame_var _ (by decide))

def command (arrays scalars : List String) (root : ℕ) : Com :=
  .ite (.eq (.var "stack.words") (.lit 0)) (.assign "machine.phase" (.lit root)) (pop arrays scalars)

theorem root_spec (B root : ℕ) (arrays scalars : List String) (hB : root+1<B) :
    Spec B (fun σ => σ.vars "stack.words"=0) (command arrays scalars root)
      (fun σ τ => τ.vars "machine.phase"=root ∧ τ.vars "recursion.return.tag"=σ.vars "recursion.return.tag" ∧
        τ.vars "recursion.return.mask"=σ.vars "recursion.return.mask" ∧ τ=σ.setVar "machine.phase" root) 6 := by
  intro σ hs
  let τ := σ.setVar "machine.phase" root
  have rr : Run B (.assign "machine.phase" (.lit root)) σ τ 2 := Run.assign (evalB_lit (show root<B by omega))
  have hc : (Cond.eq (.var "stack.words") (.lit 0)).evalB B σ=some true := by
    have hh := evalB_condEq
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ (by omega : 0<B)⟩) (evalB_lit (show 0<B by omega))
    simpa using hh
  exact ⟨τ,(Run.ite_true (d:=pop arrays scalars) hc rr).mono (by simp [Cond.size,Expr.size]),
    by simp [τ],rr.frame_var _ (by simp [Com.wvars]),rr.frame_var _ (by simp [Com.wvars]),rfl⟩

/-- The nonempty stack branch of the actual return dispatcher pops exactly
one parent frame and retains the child's return value. -/
theorem child_spec (B S root : ℕ) (arrays scalars : List String) (front : List ℕ) (saved : Env)
    (ha : "recursion.frames"∉arrays) (harrays : arrays.Nodup) (hscalars : scalars.Nodup)
    (hv : "stack.read.i"∉scalars) (hw : "stack.words"∉scalars)
    (htag : "recursion.return.tag"∉scalars) (hmask : "recursion.return.mask"∉scalars)
    (hsaved : NativeStateBounds.Bounded B saved)
    (hext : ∀ a∈arrays,(saved.arrs a).length=S)
    (hpos : 0<front.length+S*arrays.length+scalars.length)
    (hB : front.length+S*arrays.length+scalars.length+2<B) :
    Spec B (fun σ => Prefix (front++NativeRecursionFrame.words arrays scalars saved) "recursion.frames" σ ∧
      σ.vars "stack.words"=front.length+S*arrays.length+scalars.length ∧
      σ.vars "frame.length"=S*arrays.length+scalars.length ∧ σ.vars "recursion.stride"=S ∧
      ∀ a∈arrays,(σ.arrs a).length=S) (command arrays scalars root)
      (fun σ τ => Prefix front "recursion.frames" τ ∧
        (∀ a∈arrays,τ.arrs a=saved.arrs a) ∧ (∀ s∈scalars,τ.vars s=saved.vars s) ∧
        τ.vars "stack.words"=front.length ∧ τ.vars "recursion.return.tag"=σ.vars "recursion.return.tag" ∧
        τ.vars "recursion.return.mask"=σ.vars "recursion.return.mask")
      ((16*S+16)*arrays.length+7*scalars.length+12) := by
  intro σ hσ
  obtain ⟨τ,rr,hτ⟩ := pop_spec B S arrays scalars front saved ha harrays hscalars hv hw htag hmask
    hsaved hext hB σ hσ
  have hc : (Cond.eq (.var "stack.words") (.lit 0)).evalB B σ=some false := by
    have hh := evalB_condEq
      (show (Expr.var "stack.words").evalB B σ=some (front.length+S*arrays.length+scalars.length) by
        rw [evalB_var_iff]; exact ⟨hσ.2.1.symm,hσ.2.1 ▸ (by omega)⟩)
      (evalB_lit (show 0<B by omega))
    have hz : (front.length+S*arrays.length+scalars.length == 0)=false := by
      exact beq_eq_false_iff_ne.mpr (by omega)
    simpa only [hz] using hh
  exact ⟨τ,(Run.ite_false (c:=.assign "machine.phase" (.lit root)) hc rr).mono
    (by simp [Cond.size,Expr.size]; omega),hτ⟩

end Lax263307Proofs.NativeStackReturn
