import Lax263307Proofs.NativeSumHeight

namespace Lax263307Proofs.NativeSignedAccumulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational NativeSignedArithmetic

def command : Com := .seq (save "right")
  (.seq (load "sum.value") (.seq (save "left") (.seq addFraction (save "sum.value"))))

/-- Add the actual rational entry to a stored exact signed accumulator.
Both the reduced numerator/denominator and the native source cost are
controlled by the uniform bound on the two operands. -/
theorem command_spec (B M : ℕ) (a b : ℚ) (hB : 2*M^2+3<B)
    (ha : Bounded M a) (hb : Bounded M b) :
    Spec B (fun σ => Stored "sum.value" a σ ∧ FractionOutput b σ) command
      (fun _ τ => Stored "sum.value" (a+b) τ ∧ FractionOutput (a+b) τ)
      (36*(M^2).size+120) := by
  have h1 : 1<B := by nlinarith
  have hM : M<B := by nlinarith
  rintro σ ⟨hs,hbσ⟩
  obtain ⟨ν,r1,p1⟩ := save_spec B "right" b h1
    (hb.1.trans_lt hM) (hb.2.trans_lt hM) (by decide) σ hbσ
  have hsν : Stored "sum.value" a ν := by
    simpa only [Stored,String.reduceAppend,r1.frame_var "sum.value.s" (by decide),
      r1.frame_var "sum.value.n" (by decide),r1.frame_var "sum.value.d" (by decide)] using hs
  obtain ⟨μ,r2,p2⟩ := load_spec B "sum.value" a h1
    (ha.1.trans_lt hM) (ha.2.trans_lt hM) (by decide) ν hsν
  obtain ⟨ξ,r3,p3⟩ := save_spec B "left" a h1
    (ha.1.trans_lt hM) (ha.2.trans_lt hM) (by decide) μ p2
  have hbξ : Stored "right" b ξ := by
    simpa only [Stored,String.reduceAppend,(r2.seq r3).frame_var "right.s" (by decide),
      (r2.seq r3).frame_var "right.n" (by decide),(r2.seq r3).frame_var "right.d" (by decide)] using p1
  obtain ⟨υ,r4,p4⟩ := add_spec B M a b hB ha hb ξ ⟨p3,hbξ⟩
  have hab := NativeRationalBounds.add M a b ha hb
  obtain ⟨τ,r5,p5⟩ := save_spec B "sum.value" (a+b) h1
    (hab.1.trans_lt (by omega)) (hab.2.trans_lt (by omega)) (by decide) υ p4
  have hden : (a.den*b.den).size≤(M^2).size :=
    Nat.size_le_size (by nlinarith [Nat.mul_le_mul ha.2 hb.2])
  have rr := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  refine ⟨τ,rr.mono (by omega),p5,?_⟩
  simpa only [FractionOutput,r5.frame_var "rat.s" (by decide),
    r5.frame_var "rat.n" (by decide),r5.frame_var "rat.d" (by decide)] using p4

end Lax263307Proofs.NativeSignedAccumulate
