import Lax263307Proofs.NativeOracleCalls

namespace Lax263307Proofs.NativeOracleFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs

/-- The virtual machine and its input wrapper only mutate their own four
arrays; all algorithm data can therefore survive a black-box solver call. -/
theorem instruction_array (i : Lax808846.Ram.Instr) (a : String)
    (ha : a ∉ ["vm.addresses","vm.values","vm.output"]) :
    a ∉ (RamVirtualProgram.instruction i).warrs := by
  cases i <;> simp_all [RamVirtualProgram.instruction,RamVirtualProgram.binary,
    RamVirtualProgram.operands,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.warrs]

theorem dispatch_array (p : Lax808846.Ram.Program) (offset : ℕ) (a : String)
    (ha : a ∉ ["vm.addresses","vm.values","vm.output"]) :
    a ∉ (RamVirtualProgram.dispatch p offset).warrs := by
  induction p generalizing offset with
  | nil => simp [RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.warrs]
  | cons i p ih =>
    simpa only [RamVirtualProgram.dispatch,Com.warrs,List.mem_append,not_or] using
      And.intro (instruction_array i a ha) (ih (offset+1))

theorem command_array (p : Lax808846.Ram.Program) (coeff : List ℕ) (a : String)
    (ha : a ∉ ["vm.addresses","vm.values","vm.output","vm.input"]) :
    a ∉ (NativeOracleCalls.command p coeff).warrs := by
  have hm : a ∉ ["vm.addresses","vm.values","vm.output"] := by simp_all
  have hd := dispatch_array p 0 a hm
  simp_all [NativeOracleCalls.command,RamLpPrepare.command,RamBitSize.array,
    RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,
    RamPolynomial.arrays_frame,RamLpInputFrame.command,RamLpInputFrame.step,
    RamWordBuffer.append,RamVirtualProgram.execute,RamWordOps.modulus,
    RamVirtualProgram.initCommand,Com.warrs]

theorem frame_array {B K : ℕ} {σ τ : Env} {p : Lax808846.Ram.Program}
    {coeff : List ℕ} (hr : Run B (NativeOracleCalls.command p coeff) σ τ K)
    (a : String) (ha : a ∉ ["vm.addresses","vm.values","vm.output","vm.input"]) :
    τ.arrs a=σ.arrs a := hr.frame_arr a (command_array p coeff a ha)

end Lax263307Proofs.NativeOracleFrame
