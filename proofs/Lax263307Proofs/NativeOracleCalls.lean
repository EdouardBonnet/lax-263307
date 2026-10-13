import Lax455465Proofs.SparseRam
import Lax455465Proofs.RamVirtualExecution
import Lax455465Proofs.RamVirtualConstants
import Lax455465Proofs.RamLpPrepare

namespace Lax263307Proofs.NativeOracleCalls

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

/-- This generic invocation preserves the specific function chosen in the
functional algorithm. It applies equally to the LP and flow solvers. -/
def command (p : Lax808846.Ram.Program) (coefficients : List ℕ) : Com :=
  .seq (RamLpPrepare.command coefficients) (RamVirtualProgram.execute p)

theorem exists_invocation (f : List ℕ → List ℕ) (hf : RamPolytime f) :
    ∃ (p : Lax808846.Ram.Program) (wordBound timeBound : Polynomial ℕ) (coefficients : List ℕ),
    (∀ x : ℕ, RamPolynomial.value coefficients x=wordBound.eval x) ∧
    ∀ x : List ℕ,
    FitsInWords (wordBound.eval (bitSize x)) ((x.length::x)++f x) ∧
    ∀ B : ℕ,
      bitSize x+1<B → wordBound.eval (bitSize x+1)<B →
      2*(2^wordBound.eval (bitSize x))^2+3<B →
      timeBound.eval (bitSize x)+1<B → RamVirtualConstants.allowance p<B →
      Spec B (fun σ => Prefix x "lp.word" σ ∧ σ.vars "lp.position"=x.length ∧
        x.length<(σ.arrs "vm.input").length ∧
        timeBound.eval (bitSize x)<(σ.arrs "vm.addresses").length ∧
        timeBound.eval (bitSize x)<(σ.arrs "vm.values").length ∧
        timeBound.eval (bitSize x)<(σ.arrs "vm.output").length)
        (command p coefficients)
        (fun _ τ => Prefix (f x) "vm.output" τ ∧ τ.vars "vm.outputLength"=(f x).length ∧
          τ.vars "vm.running"=0)
        (((12*bitSize x+39)*x.length+6*coefficients.length+29)+
          ((timeBound.eval (bitSize x)+1)*(4*p.length+32*timeBound.eval (bitSize x)+104)+18)) := by
  obtain ⟨p,wp,tp,hprogram⟩ := SparseRam.polynomial_execution f hf
  obtain ⟨coeff,hcoeff⟩ := RamPolynomial.exists_coefficients wp
  refine ⟨p,wp,tp,coeff,hcoeff,?_⟩
  intro x
  obtain ⟨hfit,k,hk,s,hrun,hhalt,hout,_⟩ := hprogram x
  refine ⟨hfit,?_⟩
  intro B hsize hpoly hB htime hallow
  let w := wp.eval (bitSize x)
  let T := tp.eval (bitSize x)
  have hM : 2^w<B := by nlinarith [Nat.two_pow_pos w]
  have hinput : FitsInWords w (x.length::x) := fun z hz => hfit z (List.mem_append_left _ hz)
  have hlenWord : x.length<2^w := hinput _ List.mem_cons_self
  have hlen : (x.length::x).length<B := by simp only [List.length_cons]; omega
  have hwords : ∀ z∈x,z<B := fun z hz =>
    (hinput z (List.mem_cons_of_mem _ hz)).trans hM
  have hphysical : ∀ z∈(x.length::x),z<B := fun z hz => (hinput z hz).trans hM
  have hp : p.length+1<B := (RamVirtualConstants.length_bound p).trans hallow
  have hlit : ∀ i∈p,RamVirtualInstruction.LiteralsFit (B-1) i := fun i hi =>
    RamVirtualTraceBounds.literals_mono i (RamVirtualConstants.literals_fit p i hi) (by omega)
  have hnative := RamVirtualExecution.execute_spec B w k p (x.length::x) s hB (by omega) hp hlit
    hlen hphysical hrun hhalt
  have hprepare := RamLpPrepare.command_spec B coeff x (by omega) (by omega)
    hsize hwords (by simpa only [hcoeff] using hpoly)
  rintro σ ⟨hprefix,hpos,hroom,hA,hV,hO⟩
  obtain ⟨ν,r1,p1⟩ := hprepare σ ⟨hprefix,hpos,hroom⟩
  have hAν : k<(ν.arrs "vm.addresses").length := by
    rw [RamFrames.run_array_length r1]; omega
  have hVν : k<(ν.arrs "vm.values").length := by
    rw [RamFrames.run_array_length r1]; omega
  have hOν : k<(ν.arrs "vm.output").length := by
    rw [RamFrames.run_array_length r1]; omega
  obtain ⟨τ,r2,p2⟩ := hnative ν ⟨by simpa only [hcoeff] using p1.1,p1.2.1,p1.2.2,hAν,hVν,hOν⟩
  have hcost := Nat.mul_le_mul (Nat.add_le_add_right hk 1)
    (show 4*p.length+32*k+104≤4*p.length+32*T+104 by omega)
  refine ⟨τ,(r1.seq r2).mono (by dsimp only [T] at hcost; omega),?_,?_,p2.2⟩
  · simpa only [hout] using p2.1.2.2.2.2.2.1
  · simpa only [hout] using p2.1.2.2.2.2.2.2

end Lax263307Proofs.NativeOracleCalls
