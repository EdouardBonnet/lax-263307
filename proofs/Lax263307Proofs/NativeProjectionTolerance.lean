import Lax263307Proofs.NativeRationalRead
import Lax263307Proofs.NativeSignedArithmetic

namespace Lax263307Proofs.NativeProjectionTolerance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding NativeSignedArithmetic

def command : Com := .seq (.assign "read.cursor" (.lit 0))
  (.seq (NativeRationalRead.command "projection.tolerance") (save "projection.tolerance"))

theorem command_spec (B : ℕ) (ρ : ℚ) (h3 : 3<B) (hn : ρ.num.natAbs<B) (hd : ρ.den<B) :
    Spec B (Prefix (encodeRational ρ) "projection.tolerance") command
      (fun _ τ => Stored "projection.tolerance" ρ τ) 25 := by
  intro σ hp
  have r1 : Run B (.assign "read.cursor" (.lit 0)) σ (σ.setVar "read.cursor" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨ν,r2,p2⟩ := NativeRationalRead.command_spec B "projection.tolerance" ρ [] [] h3
    (by simpa using h3) hn hd (σ.setVar "read.cursor" 0) ⟨by simpa only [List.nil_append,List.append_nil,Prefix,arrs_setVar] using hp,by simp⟩
  obtain ⟨τ,r3,p3⟩ := save_spec B "projection.tolerance" ρ (by omega) hn hd (by decide) ν p2.1
  exact ⟨τ,r1.seq (r2.seq r3),p3⟩

end Lax263307Proofs.NativeProjectionTolerance
