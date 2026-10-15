import Lax263307Proofs.NativeCoreMachine

set_option maxHeartbeats 250000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeCoreOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs NativeCoreMachine

theorem instruction (i : Lax808846.Ram.Instr) : (RamVirtualProgram.instruction i).NoWrite := by
  cases i with
  | set x0 x1 => change (RamVirtualProgram.instruction (.set 0 0)).NoWrite; decide
  | load x0 x1 => change (RamVirtualProgram.instruction (.load 0 0)).NoWrite; decide
  | store x0 x1 => change (RamVirtualProgram.instruction (.store 0 0)).NoWrite; decide
  | add x0 x1 x2 => change (RamVirtualProgram.instruction (.add 0 0 0)).NoWrite; decide
  | sub x0 x1 x2 => change (RamVirtualProgram.instruction (.sub 0 0 0)).NoWrite; decide
  | mul x0 x1 x2 => change (RamVirtualProgram.instruction (.mul 0 0 0)).NoWrite; decide
  | div x0 x1 x2 => change (RamVirtualProgram.instruction (.div 0 0 0)).NoWrite; decide
  | and x0 x1 x2 => change (RamVirtualProgram.instruction (.and 0 0 0)).NoWrite; decide
  | shiftl x0 x1 x2 => change (RamVirtualProgram.instruction (.shiftl 0 0 0)).NoWrite; decide
  | not x0 x1 => change (RamVirtualProgram.instruction (.not 0 0)).NoWrite; decide
  | jump x0 => change (RamVirtualProgram.instruction (.jump 0)).NoWrite; decide
  | jzero x0 x1 => change (RamVirtualProgram.instruction (.jzero 0 0)).NoWrite; decide
  | jeof x0 => change (RamVirtualProgram.instruction (.jeof 0)).NoWrite; decide
  | inputLength x0 => change (RamVirtualProgram.instruction (.inputLength 0)).NoWrite; decide
  | inputLoad x0 x1 => change (RamVirtualProgram.instruction (.inputLoad 0 0)).NoWrite; decide
  | halt  => change (RamVirtualProgram.instruction (.halt )).NoWrite; decide
  | read x0 => change (RamVirtualProgram.instruction (.read 0)).NoWrite; decide
  | write x0 => change (RamVirtualProgram.instruction (.write 0)).NoWrite; decide

theorem virtual_dispatch (p : Lax808846.Ram.Program) (i : ℕ) : (RamVirtualProgram.dispatch p i).NoWrite := by
  induction p generalizing i with
  | nil => change RamVirtualProgram.stop.NoWrite; decide
  | cons x xs ih => exact ⟨instruction x,ih (i+1)⟩

theorem virtual (p : Lax808846.Ram.Program) : (RamVirtualProgram.execute p).NoWrite := by
  exact ⟨by decide,by decide,virtual_dispatch p 0⟩

theorem polynomial (cs : List ℕ) : (RamPolynomial.command cs).NoWrite := by
  induction cs with
  | nil => decide
  | cons c cs ih => exact ⟨ih,trivial⟩

theorem call (p : Lax808846.Ram.Program) (cs : List ℕ) : (NativeOracleCalls.command p cs).NoWrite := by
  exact ⟨⟨by decide,trivial,polynomial cs,trivial,by decide⟩,virtual p⟩

theorem projection (p : Lax808846.Ram.Program) (cs : List ℕ) :
    (NativeProjectionOracle.command p cs).NoWrite := by
  exact ⟨⟨by decide,call p cs⟩,by decide,by decide⟩

theorem cut_callback (p : Lax808846.Ram.Program) (cs : List ℕ) :
    (NativeSeparatorContext.callback p cs).NoWrite := by
  exact ⟨by decide,⟨by decide,call p cs⟩,by decide⟩

theorem cut_loop (c : Com) (h : c.NoWrite) : (NativeCutLoop.command c).NoWrite := by
  simp only [NativeCutLoop.command,NativeCutLoop.step,NativeCutLoop.branch,Com.NoWrite,h,true_and,and_true]
  decide

theorem separator (p : Lax808846.Ram.Program) (cs : List ℕ) :
    (NativeSeparatorOutput.command p cs).NoWrite := by
  exact ⟨by decide,cut_loop _ (cut_callback p cs),by decide⟩

theorem rounded (p : Lax808846.Ram.Program) : (NativeRoundedControl.command p 4 14).NoWrite := by
  exact ⟨trivial,⟨by decide,⟨by decide,virtual p⟩,by decide⟩,by decide⟩

theorem save_arrays (as : List String) : (NativeFrameBuffers.save as).NoWrite := by
  induction as with
  | nil => decide
  | cons a as ih =>
    refine ⟨⟨trivial,?_⟩,ih⟩
    change (NativeBlockAppend.command "" "recursion.frames").NoWrite
    decide

theorem save_scalars (ss : List String) : (NativeFrameScalars.save ss).NoWrite := by
  induction ss with
  | nil => decide
  | cons s ss ih =>
    change (RamWordBuffer.append "recursion.frames" "stack.words" (.lit 0)).NoWrite ∧ (NativeFrameScalars.save ss).NoWrite
    exact ⟨by decide,ih⟩

theorem restore_arrays (as : List String) : (NativeFrameBufferRestore.command as).NoWrite := by
  induction as with
  | nil => decide
  | cons a as ih =>
    refine ⟨⟨trivial,?_⟩,ih⟩
    change (NativeBlockRestore.command "").NoWrite
    decide

theorem restore_scalars (ss : List String) : (NativeFrameRestore.command ss).NoWrite := by
  induction ss with
  | nil => decide
  | cons s ss ih => exact ⟨⟨trivial,trivial⟩,ih⟩

theorem child_call (arrays scalars : List String) : (NativeChildCall.command arrays scalars 1 12).NoWrite := by
  exact ⟨trivial,⟨save_arrays arrays,save_scalars scalars⟩,by decide,by decide⟩

theorem stack_return (arrays scalars : List String) : (NativeStackReturn.command arrays scalars 15).NoWrite := by
  exact ⟨trivial,⟨trivial,trivial⟩,restore_arrays arrays,restore_scalars scalars⟩

theorem phase (cfg : Config) (c : Com) (hc : c∈phases cfg) : c.NoWrite := by
  simp only [phases,cases,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · decide
  · change (NativeNodeDispatch.command 0 0 0 2 3 14).NoWrite; decide
  · decide
  · change ((NativeLargeNode.command 0 0 0).seq (go 4)).NoWrite; decide
  · exact ⟨by decide,projection cfg.lp cfg.lpWidth,trivial⟩
  · decide
  · decide
  · decide
  · exact ⟨separator cfg.flow cfg.flowWidth,by decide⟩
  · decide
  · decide
  · exact ⟨by decide,child_call (frameArrays cfg) (frameScalars cfg)⟩
  · decide
  · exact rounded cfg.rounded
  · exact stack_return (frameArrays cfg) (frameScalars cfg)
  · decide

theorem dispatch (cs : List Com) (h : ∀ c∈cs,c.NoWrite) (i : ℕ) :
    (NativeMachineTrace.dispatch cs i).NoWrite := by
  induction cs generalizing i with
  | nil => trivial
  | cons c cs ih => exact ⟨h c (by simp),ih (fun d hd => h d (by simp [hd])) _⟩

theorem command (cfg : Config) : (NativeCoreMachine.command cfg).NoWrite := by
  exact ⟨trivial,by decide,dispatch (phases cfg) (phase cfg) 0⟩

end Lax263307Proofs.NativeCoreOutput
