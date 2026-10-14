import Lax263307Proofs.NativeMomentProgram
import Lax263307Proofs.NativeOutputBounds
import Lax455465Proofs.WordSize

namespace Lax263307Proofs.NativeMomentEncodingHeight

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 MomentLP NativeCatalogMetadata
open Lax109476.RationalEncoding
open Lax455465Proofs

def height (n k r : ℕ) : ℕ := 100*(NativeMomentProgram.size n k r)^3+10

/-- The checked native constructor establishes a polynomial height bound
on every actual moment-LP word, including all coefficients and dimensions. -/
theorem program_words {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    ∀ z∈encodeProgram (program G k r),z<2^height n k r := by
  let X := NativeMomentProgram.size n k r
  let v := height n k r
  let B := 2^v
  let ext := fun (_ : String) => NativeMomentSetup.guardBound n k r
  let input := NativeMomentProgram.encodeInput G k r
  let σ := initEnv ext input
  have hX : 1≤X := by dsimp [X,NativeMomentProgram.size]; omega
  have h13 : X≤X^3 := le_self_pow hX (by omega)
  have hnX : n≤X := by dsimp [X,NativeMomentProgram.size]; omega
  have hguard : NativeMomentSetup.guardBound n k r<v := by
    have hg := (NativeMomentProgram.polynomial_bounds n k r).1
    change _≤73*X^3 at hg
    change NativeMomentSetup.guardBound n k r<100*X^3+10
    omega
  have hB : NativeMomentSetup.guardBound n k r<B := hguard.trans Nat.lt_two_pow_self
  have hm : 2^n<B := Nat.pow_lt_pow_right (by decide) (by dsimp [v,height]; nlinarith only [h13,hnX])
  have hσ : NativeArrayBounds.Bounded B σ := by
    intro a z hz
    have he : z=0 := List.eq_of_mem_replicate hz
    subst z
    exact Nat.two_pow_pos v
  obtain ⟨τ,rr,ho⟩ := NativeMomentProgram.full_command_spec B G k r hB hm σ
    ⟨rfl,hσ,by intro a; simp [σ,initEnv,ext]⟩
  have hb := NativeOutputBounds.run rr (by simp [σ,initEnv])
  simpa only [ho,σ,initEnv,List.nil_append] using hb

end Lax263307Proofs.NativeMomentEncodingHeight
