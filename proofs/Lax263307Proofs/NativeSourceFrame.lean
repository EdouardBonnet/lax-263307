import Lax263307Proofs.NativeCoreFrame
import Lax263307Proofs.NativeOracleRounds

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSourceFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeCoreMachine

theorem base_input_n (cfg : Config) (c : Com) (hc : c∈cases cfg [] []) :
    "input.n"∉c.wvars := by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "input.n"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars; decide
  · decide
  · change "input.n"∉((NativeLargeNode.command 0 0 0).seq (go 4)).wvars; decide
  · exact NativeOracleExecution.projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem base_blowup_length (cfg : Config) (c : Com) (hc : c∈cases cfg [] []) :
    "blowup.length"∉c.wvars := by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "blowup.length"∉(NativeNodeDispatch.command 0 0 0 2 3 14).wvars; decide
  · decide
  · change "blowup.length"∉((NativeLargeNode.command 0 0 0).seq (go 4)).wvars; decide
  · exact NativeOracleExecution.projection_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_variable cfg _ (by decide) (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_variable _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_variable cfg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem base_blowup_owner (cfg : Config) (c : Com) (hc : c∈cases cfg [] []) :
    "blowup.owner"∉c.warrs := by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "blowup.owner"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs; decide
  · decide
  · change "blowup.owner"∉((NativeLargeNode.command 0 0 0).seq (go 4)).warrs; decide
  · exact NativeOracleExecution.projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_array cfg _ (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_array cfg _ (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem base_image_output (cfg : Config) (c : Com) (hc : c∈cases cfg [] []) :
    "image.output"∉c.warrs := by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "image.output"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs; decide
  · decide
  · change "image.output"∉((NativeLargeNode.command 0 0 0).seq (go 4)).warrs; decide
  · exact NativeOracleExecution.projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_array cfg _ (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_array cfg _ (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem base_weighted_output (cfg : Config) (c : Com) (hc : c∈cases cfg [] []) :
    "weighted.output"∉c.warrs := by
  simp only [cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change "weighted.output"∉(NativeNodeDispatch.command 0 0 0 2 3 14).warrs; decide
  · decide
  · change "weighted.output"∉((NativeLargeNode.command 0 0 0).seq (go 4)).warrs; decide
  · exact NativeOracleExecution.projection_array cfg _ (by decide) (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide
  · decide
  · exact NativeNearExecution.separator_array cfg _ (by decide) (by decide) (by decide)
      (NativeSeparatorContext.callback_array _ _ _ (by decide) (by decide) (by decide) (by decide)) (by decide)
  · decide
  · decide
  · decide
  · decide
  · exact NativeOracleRounds.update_array cfg _ (by decide) (by decide) (by decide) (by decide)
  · decide
  · decide

theorem scalar_unsaved (cfg : Config) (s : String) (hs : s∈["input.n","blowup.length"]) :
    s∉frameScalars cfg := by
  intro h
  simp only [frameScalars,List.mem_filter,List.mem_dedup] at h
  obtain ⟨c,hc,hw⟩ := List.mem_flatMap.mp h.1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl
  · exact base_input_n cfg c hc hw
  · exact base_blowup_length cfg c hc hw

theorem array_unsaved (cfg : Config) (a : String)
    (ha : a∈["blowup.owner","image.output","weighted.output"]) : a∉frameArrays cfg := by
  intro h
  simp only [frameArrays,List.mem_filter,List.mem_dedup] at h
  obtain ⟨c,hc,hw⟩ := List.mem_flatMap.mp h.1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl
  · exact base_blowup_owner cfg c hc hw
  · exact base_image_output cfg c hc hw
  · exact base_weighted_output cfg c hc hw

theorem dispatch_variable (cs : List Com) (s : String) (hs : s≠"machine.running")
    (h : ∀ c∈cs,s∉c.wvars) (i : ℕ) : s∉(NativeMachineTrace.dispatch cs i).wvars := by
  induction cs generalizing i with
  | nil => simpa [NativeMachineTrace.dispatch,Com.wvars] using hs
  | cons c cs ih =>
    simp only [NativeMachineTrace.dispatch,Com.wvars,List.mem_append,not_or]
    exact ⟨h c (by simp),ih (fun d hd => h d (by simp [hd])) _⟩

theorem dispatch_array (cs : List Com) (a : String) (h : ∀ c∈cs,a∉c.warrs) (i : ℕ) :
    a∉(NativeMachineTrace.dispatch cs i).warrs := by
  induction cs generalizing i with
  | nil => simp [NativeMachineTrace.dispatch,Com.warrs]
  | cons c cs ih =>
    simp only [NativeMachineTrace.dispatch,Com.warrs,List.mem_append,not_or]
    exact ⟨h c (by simp),ih (fun d hd => h d (by simp [hd])) _⟩

theorem command_variable (cfg : Config) (s : String) (hs : s∈["input.n","blowup.length"]) :
    s∉(command cfg).wvars := by
  have he : s∉excludedScalars := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl <;> decide
  have hphases := NativeCoreFrame.scalar_unwritten cfg s (scalar_unsaved cfg s hs) he
  have hr : s≠"machine.running" := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl <;> decide
  have hdriver := dispatch_variable (phases cfg) s hr hphases 0
  simp only [command,NativeMachineTrace.driver,Com.wvars,List.mem_append,not_or]
  refine ⟨?_,?_,hdriver⟩
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl|rfl <;> simp [frameSize,initializeRoot,go,Com.wvars]

theorem command_array (cfg : Config) (a : String)
    (ha : a∈["blowup.owner","image.output","weighted.output"]) : a∉(command cfg).warrs := by
  have he : a≠"recursion.frames" := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> decide
  have hphases := NativeCoreFrame.array_unwritten cfg a (array_unsaved cfg a ha) he
  have hdriver := dispatch_array (phases cfg) a hphases 0
  simpa only [command,frameSize,initializeRoot,go,NativeMachineTrace.driver,Com.warrs,
    List.nil_append,List.not_mem_nil,not_false_eq_true,not_or] using hdriver

end Lax263307Proofs.NativeSourceFrame
