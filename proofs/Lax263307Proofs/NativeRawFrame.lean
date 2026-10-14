import Lax263307Proofs.NativeRawOracle
import Lax263307Proofs.NativeOracleScalars
import Lax263307Proofs.NativeOracleFrame

namespace Lax263307Proofs.NativeRawFrame

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem command_variable (p : Lax808846.Ram.Program) (s : String)
    (hpre : s∉NativeRawOracle.prepare.wvars) (hvm : s∉NativeOracleScalars.reserved) :
    s∉(NativeRawOracle.command p).wvars := by
  have hv := NativeOracleScalars.command_variable p [] s hvm
  simp only [NativeOracleCalls.command,Com.wvars,List.mem_append,not_or] at hv
  simpa only [NativeRawOracle.command,Com.wvars,List.mem_append,not_or] using And.intro hpre hv.2

theorem array (p : Lax808846.Ram.Program) (a : String)
    (hpre : a∉NativeRawOracle.prepare.warrs)
    (hvm : a∉["vm.addresses","vm.values","vm.output","vm.input"]) :
    a∉(NativeRawOracle.command p).warrs := by
  have hv := NativeOracleFrame.command_array p [] a hvm
  simp only [NativeOracleCalls.command,Com.warrs,List.mem_append,not_or] at hv
  simpa only [NativeRawOracle.command,Com.warrs,List.mem_append,not_or] using And.intro hpre hv.2

end Lax263307Proofs.NativeRawFrame
