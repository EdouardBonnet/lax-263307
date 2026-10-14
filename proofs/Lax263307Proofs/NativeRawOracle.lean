import Lax263307Proofs.NativeOracleCalls
import Lax263307Proofs.NativeSlice

namespace Lax263307Proofs.NativeRawOracle

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def setup : Com := .seq (.assign "fill.length" (.var "lp.position")) (.assign "slice.start" (.lit 0))

def prepare : Com := .seq setup (.seq (NativeSlice.command "lp.word" "vm.input")
  (.assign "vm.inputLength" (.var "lp.position")))

theorem setup_spec (B count : ℕ) (hB : count+2<B) :
    Spec B (fun σ => σ.vars "lp.position"=count) setup
      (fun _ τ => τ.vars "fill.length"=count ∧ τ.vars "slice.start"=0) 4 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]

theorem prepare_spec (B : ℕ) (xs : List ℕ) (hB : xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Prefix xs "lp.word" σ ∧ σ.vars "lp.position"=xs.length ∧
      xs.length≤(σ.arrs "vm.input").length) prepare
      (fun _ τ => Prefix xs "vm.input" τ ∧ τ.vars "vm.inputLength"=xs.length) (16*xs.length+12) := by
  rintro σ ⟨hp,hlen,hroom⟩
  obtain ⟨ν,r1,p1⟩ := setup_spec B xs.length hB σ hlen
  obtain ⟨μ,r2,p2⟩ := NativeSlice.command_spec B "lp.word" "vm.input" [] xs [] (by decide) (by simp; omega) hv ν
    ⟨⟨by simpa only [List.nil_append,List.append_nil,Prefix,r1.frame_arr "lp.word" (by decide)] using hp,
      by simpa only [List.length_nil] using p1.2⟩,p1.1,by rwa [RamFrames.run_array_length r1]⟩
  have hlenμ := ((r1.seq r2).frame_var "lp.position" (by decide)).trans hlen
  let τ := μ.setVar "vm.inputLength" xs.length
  have r3 : Run B (.assign "vm.inputLength" (.var "lp.position")) μ τ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hlenμ.symm,hlenμ ▸ (by omega : xs.length<B)⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),by simpa only [Prefix,τ,arrs_setVar] using p2.2,by simp [τ]⟩

def command (p : Lax808846.Ram.Program) : Com := .seq prepare (RamVirtualProgram.execute p)

def cost (p : Lax808846.Ram.Program) (length T : ℕ) : ℕ :=
  16*length+12+(T+1)*(4*p.length+32*T+104)+18

/-- Invoke an actual fixed registered RAM program on its raw input
format. A bounded execution on this particular input suffices; no
polynomial-time guarantee on arbitrary malformed inputs is needed. -/
theorem command_spec (B w T : ℕ) (p : Lax808846.Ram.Program) (xs ys : List ℕ)
    (hB : 2*(2^w)^2+3<B) (hT : T+1<B) (hp : RamVirtualConstants.allowance p<B)
    (hlen : xs.length+2<B) (hv : ∀ z∈xs,z<B)
    (hrun : ∃ t≤T,Lax808846.Ram.RunsTo w p xs ys t) :
    Spec B (fun σ => Prefix xs "lp.word" σ ∧ σ.vars "lp.position"=xs.length ∧
      σ.vars "vm.width"=w ∧ xs.length≤(σ.arrs "vm.input").length ∧
      T<(σ.arrs "vm.addresses").length ∧ T<(σ.arrs "vm.values").length ∧ T<(σ.arrs "vm.output").length)
      (command p) (fun _ τ => Prefix ys "vm.output" τ ∧ τ.vars "vm.outputLength"=ys.length ∧
        τ.vars "vm.running"=0) (cost p xs.length T) := by
  obtain ⟨t,ht,hrun⟩ := hrun
  obtain ⟨k,hkt,s,hs,hhalt,hout,_,_⟩ := SparseRam.exists_execution w p xs ys t hrun
  have hk : k≤T := hkt.trans ht
  have hpLen : p.length+1<B := (RamVirtualConstants.length_bound p).trans hp
  have hlit : ∀ i∈p,RamVirtualInstruction.LiteralsFit (B-1) i := fun i hi =>
    RamVirtualTraceBounds.literals_mono i (RamVirtualConstants.literals_fit p i hi) (by omega)
  have hnative := RamVirtualExecution.execute_spec B w k p xs s hB (by omega) hpLen hlit (by omega) hv hs hhalt
  rintro σ ⟨hprefix,hpos,hwidth,hinput,hA,hV,hO⟩
  obtain ⟨ν,r1,p1⟩ := prepare_spec B xs hlen hv σ ⟨hprefix,hpos,hinput⟩
  obtain ⟨τ,r2,p2⟩ := hnative ν
    ⟨(r1.frame_var "vm.width" (by decide)).trans hwidth,p1.1,p1.2,
      by rw [RamFrames.run_array_length r1]; omega,
      by rw [RamFrames.run_array_length r1]; omega,
      by rw [RamFrames.run_array_length r1]; omega⟩
  have hcost := Nat.mul_le_mul (Nat.add_le_add_right hk 1)
    (show 4*p.length+32*k+104≤4*p.length+32*T+104 by omega)
  exact ⟨τ,(r1.seq r2).mono (by dsimp only [cost]; omega),
    by simpa only [hout] using p2.1.2.2.2.2.2.1,
    by simpa only [hout] using p2.1.2.2.2.2.2.2,p2.2⟩

end Lax263307Proofs.NativeRawOracle
