import Lax263307Proofs.NativeSlice

namespace Lax263307Proofs.NativeBlockRestore

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def setup : Com := .seq (.assign "fill.length" (.var "stack.copy.length"))
  (.assign "slice.start" (.var "stack.read.i"))

def command (target : String) : Com := .seq setup
  (.seq (NativeSlice.command "recursion.frames" target)
    (.assign "stack.read.i" (.add (.var "stack.read.i") (.var "stack.copy.length"))))

theorem setup_spec (B base count : ℕ) (hB : base+count+2<B) :
    Spec B (fun σ => σ.vars "stack.read.i"=base ∧ σ.vars "stack.copy.length"=count) setup
      (fun _ τ => τ.vars "fill.length"=count ∧ τ.vars "slice.start"=base) 4 := by
  rintro σ ⟨hb,hc⟩
  run_vcg
  all_goals simp_all [Env.setVar]

/-- Restore one initialized saved block into a working buffer. The
stack stays unchanged and the read cursor advances by its exact length. -/
theorem command_spec (B : ℕ) (target : String) (front xs : List ℕ)
    (hne : "recursion.frames"≠target) (hB : front.length+xs.length+2<B) (hv : ∀ z∈xs,z<B) :
    Spec B (fun σ => Prefix (front++xs) "recursion.frames" σ ∧
      σ.vars "stack.read.i"=front.length ∧ σ.vars "stack.copy.length"=xs.length ∧
      xs.length≤(σ.arrs target).length) (command target)
      (fun _ τ => Prefix (front++xs) "recursion.frames" τ ∧ Prefix xs target τ ∧
        τ.vars "stack.read.i"=front.length+xs.length) (16*xs.length+14) := by
  rintro σ ⟨hp,hi,hl,hroom⟩
  obtain ⟨ν,r1,p1⟩ := setup_spec B front.length xs.length hB σ ⟨hi,hl⟩
  obtain ⟨μ,r2,p2⟩ := NativeSlice.command_spec B "recursion.frames" target front xs [] hne (by omega) hv ν
    ⟨⟨by simpa only [List.append_nil,Prefix,r1.frame_arr "recursion.frames" (by decide)] using hp,p1.2⟩,
      p1.1,by rwa [RamFrames.run_array_length r1]⟩
  have hiμ := ((r1.seq r2).frame_var "stack.read.i" (by simp [setup,NativeSlice.command,
    NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.wvars])).trans hi
  have hlμ := ((r1.seq r2).frame_var "stack.copy.length" (by simp [setup,NativeSlice.command,
    NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append,Com.wvars])).trans hl
  let τ := μ.setVar "stack.read.i" (front.length+xs.length)
  have r3 : Run B (.assign "stack.read.i" (.add (.var "stack.read.i") (.var "stack.copy.length"))) μ τ 4 :=
    Run.assign (evalB_bin (op:=.add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega : front.length<B)⟩)
      (by rw [evalB_var_iff]; exact ⟨hlμ.symm,hlμ ▸ (by omega : xs.length<B)⟩)
      (by change front.length+xs.length<B; omega))
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),?_,?_,by simp [τ]⟩
  · simpa only [NativeSlice.Context,List.append_nil,Prefix,τ,arrs_setVar] using p2.1.1
  · simpa only [Prefix,τ,arrs_setVar] using p2.2

end Lax263307Proofs.NativeBlockRestore
