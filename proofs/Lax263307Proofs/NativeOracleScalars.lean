import Lax263307Proofs.NativeOracleFrame

set_option maxRecDepth 20000
set_option maxHeartbeats 700000

namespace Lax263307Proofs.NativeOracleScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax455465Proofs

def reserved : List String := ["frame.i","lookup.address","lookup.i","lookup.result","lp.position","lp.word","poly.argument","poly.value","put.address","put.value","size.count","size.i","size.total","size.value","vm.addresses","vm.count","vm.cursor","vm.input","vm.inputLength","vm.left","vm.modulus","vm.output","vm.outputLength","vm.pc","vm.result","vm.right","vm.running","vm.target","vm.values","vm.width"]

theorem instruction_variable (i : Lax808846.Ram.Instr) (x : String) (hx : x∉reserved) :
    x∉(RamVirtualProgram.instruction i).wvars := by
  cases i <;> simp_all [reserved,RamVirtualProgram.instruction,RamVirtualProgram.binary,
    RamVirtualProgram.operands,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,RamSparseMemory.lookup,
    RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.wvars]

theorem dispatch_variable (p : Lax808846.Ram.Program) (offset : ℕ) (x : String) (hx : x∉reserved) :
    x∉(RamVirtualProgram.dispatch p offset).wvars := by
  induction p generalizing offset with
  | nil => simp_all [reserved,RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.wvars]
  | cons i p ih =>
    simpa only [RamVirtualProgram.dispatch,Com.wvars,List.mem_append,not_or] using
      And.intro (instruction_variable i x hx) (ih (offset+1))

theorem command_variable (p : Lax808846.Ram.Program) (coeff : List ℕ) (x : String) (hx : x∉reserved) :
    x∉(NativeOracleCalls.command p coeff).wvars := by
  have hd := dispatch_variable p 0 x hx
  have hp := RamPolynomial.variable_frame coeff x (by simp_all [reserved])
  simp_all [reserved,NativeOracleCalls.command,RamLpPrepare.command,RamBitSize.array,
    RamBitSize.arrayStep,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,
    RamLpInputFrame.command,RamLpInputFrame.step,RamWordBuffer.append,
    RamVirtualProgram.execute,RamWordOps.modulus,RamVirtualProgram.initCommand,Com.wvars]


end Lax263307Proofs.NativeOracleScalars
