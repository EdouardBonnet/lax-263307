import Lax263307Proofs.NativeCoreMachine
import Lax263307Proofs.NativeMachineFrame

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCoreFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeCoreMachine NativeMachineSegment

theorem array_saved (cfg : Config) (a : String) (c : Com)
    (hc : c∈cases cfg [] []) (ha : a∈c.warrs) (he : a≠"recursion.frames") : a∈frameArrays cfg := by
  simp only [frameArrays,List.mem_filter,List.mem_dedup,bne_iff_ne]
  exact ⟨List.mem_flatMap.mpr ⟨c,hc,ha⟩,he⟩

theorem scratch_covered (cfg : Config) (s : String) (hs : s∈NativeStackReturn.bufferScratch) :
    s∈frameScalars cfg ∨ s∈excludedScalars := by
  have hprep : ∀ s∈["fill.length","slice.start","fill.value","fill.i"],
      s∈NativeProjectionPrepare.command.wvars := by
    intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl|rfl|rfl <;> decide
  have hsave (s : String) (hs : s∈["fill.length","slice.start","fill.value","fill.i"])
      (he : s∉excludedScalars) : s∈frameScalars cfg := by
    apply scalar_saved cfg s
      (.seq NativeProjectionPrepare.command (.seq (NativeProjectionOracle.command cfg.lp cfg.lpWidth) (go 5)))
    · simp [cases]
    · exact List.mem_append_left _ (hprep s hs)
    · exact he
  simp only [NativeStackReturn.bufferScratch,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
  · exact Or.inr (by decide)
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inl (hsave _ (by decide) (by decide))
  · exact Or.inr (by decide)

/-- The frame footprint also covers the commands introduced by wrapping
the base controller in save/restore operations. -/
theorem scalar_unwritten (cfg : Config) (s : String) (hs : s∉frameScalars cfg)
    (he : s∉excludedScalars) : ∀ c∈phases cfg,s∉c.wvars := by
  have hb (c : Com) (hc : c∈cases cfg [] []) : s∉c.wvars :=
    fun hw => hs (scalar_saved cfg s c hc hw he)
  have hsave : s∉(NativeRecursionFrame.save (frameArrays cfg) (frameScalars cfg)).wvars := by
    apply NativeChildCall.save_variable
    intro h
    apply he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> decide
  have hrestore : s∉(NativeRecursionFrame.restore (frameArrays cfg) (frameScalars cfg)).wvars :=
    NativeStackReturn.restore_variable _ _ s
      (fun h => (scratch_covered cfg s h).elim hs he) hs
  have hc := hb (Com.seq NativeChildGraph.command (NativeChildCall.command [] [] 1 12)) (by simp [cases])
  have ht := hb (NativeStackReturn.command [] [] 15) (by simp [cases])
  simp only [NativeChildCall.command,NativeStackReturn.command,NativeStackReturn.pop,
    Com.wvars,List.mem_append,not_or] at hc ht
  intro c h
  simp only [phases,cases,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | solve | apply hb; simp [cases]
    | simpa only [NativeChildCall.command,Com.wvars,List.mem_append,not_or] using
        And.intro hc.1 (And.intro hc.2.1 (And.intro hsave hc.2.2.2))
    | simpa only [NativeStackReturn.command,NativeStackReturn.pop,Com.wvars,List.mem_append,not_or] using
        And.intro ht.1 (And.intro ht.2.1 hrestore)

theorem array_unwritten (cfg : Config) (a : String) (ha : a∉frameArrays cfg)
    (he : a≠"recursion.frames") : ∀ c∈phases cfg,a∉c.warrs := by
  have hb (c : Com) (hc : c∈cases cfg [] []) : a∉c.warrs :=
    fun hw => ha (array_saved cfg a c hc hw he)
  have hsave := NativeChildCall.save_array (frameArrays cfg) (frameScalars cfg) a he
  have hrestore : a∉(NativeRecursionFrame.restore (frameArrays cfg) (frameScalars cfg)).warrs := by
    simpa only [NativeRecursionFrame.restore,Com.warrs,List.mem_append,not_or] using
      And.intro (NativeFrameBufferRestore.array_frame _ a ha) (NativeRecursionFrame.scalars_array _ a)
  have hc := hb (Com.seq NativeChildGraph.command (NativeChildCall.command [] [] 1 12)) (by simp [cases])
  have ht := hb (NativeStackReturn.command [] [] 15) (by simp [cases])
  simp only [NativeChildCall.command,NativeStackReturn.command,NativeStackReturn.pop,
    Com.warrs,List.mem_append,not_or] at hc ht
  intro c h
  simp only [phases,cases,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
    | solve | apply hb; simp [cases]
    | simpa only [NativeChildCall.command,Com.warrs,List.mem_append,not_or] using
        And.intro hc.1 (And.intro hc.2.1 (And.intro hsave hc.2.2.2))
    | simpa only [NativeStackReturn.command,NativeStackReturn.pop,Com.warrs,List.mem_append,not_or] using
        And.intro ht.1 (And.intro ht.2.1 hrestore)

/-- Every field not saved in a parent frame is either deliberate stack/return
metadata or is untouched by the whole recursive execution. -/
theorem segment_scalar {B steps total : ℕ} {cfg : Config} {σ τ : Env}
    (trace : Segment B (phases cfg) steps total σ τ) (s : String)
    (hs : s∉frameScalars cfg) (he : s∉excludedScalars) : τ.vars s=σ.vars s :=
  NativeMachineFrame.scalar trace s (scalar_unwritten cfg s hs he)

theorem segment_array {B steps total : ℕ} {cfg : Config} {σ τ : Env}
    (trace : Segment B (phases cfg) steps total σ τ) (a : String)
    (ha : a∉frameArrays cfg) (he : a≠"recursion.frames") : τ.arrs a=σ.arrs a :=
  NativeMachineFrame.array trace a (array_unwritten cfg a ha he)

/-- After a child call and return, restoring the selected frame is enough
to restore the entire parent environment outside stack/return metadata.
The snapshot is taken after preparing the child graph and setting phase 12,
exactly where NativeChildCall saves it. -/
theorem parent_restored {B steps total prepTime : ℕ} {cfg : Config} {σ saved τ : Env}
    (snapshot : Run B (Com.seq NativeChildGraph.command (go 12)) σ saved prepTime)
    (trace : Segment B (phases cfg) steps total σ τ)
    (hv : ∀ s∈frameScalars cfg,τ.vars s=saved.vars s)
    (ha : ∀ a∈frameArrays cfg,τ.arrs a=saved.arrs a) :
    (∀ s,s∉excludedScalars → τ.vars s=saved.vars s) ∧
      (∀ a,a≠"recursion.frames" → τ.arrs a=saved.arrs a) := by
  constructor
  · intro s he
    by_cases hs : s∈frameScalars cfg
    · exact hv s hs
    · have hw := scalar_unwritten cfg s hs he
        (Com.seq NativeChildGraph.command (NativeChildCall.command (frameArrays cfg) (frameScalars cfg) 1 12))
        (by simp [phases,cases])
      simp only [NativeChildCall.command,Com.wvars,List.mem_append,not_or] at hw
      have hp : s∉(Com.seq NativeChildGraph.command (go 12)).wvars := by
        simpa only [go,Com.wvars,List.mem_append,not_or] using And.intro hw.1 hw.2.1
      exact (segment_scalar trace s hs he).trans (snapshot.frame_var s hp).symm
  · intro a he
    by_cases hs : a∈frameArrays cfg
    · exact ha a hs
    · have hw := array_unwritten cfg a hs he
        (Com.seq NativeChildGraph.command (NativeChildCall.command (frameArrays cfg) (frameScalars cfg) 1 12))
        (by simp [phases,cases])
      simp only [NativeChildCall.command,Com.warrs,List.mem_append,not_or] at hw
      have hp : a∉(Com.seq NativeChildGraph.command (go 12)).warrs := by
        simpa only [go,Com.warrs,List.mem_append,not_or] using And.intro hw.1 hw.2.1
      exact (segment_array trace a hs he).trans (snapshot.frame_arr a hp).symm

end Lax263307Proofs.NativeCoreFrame
