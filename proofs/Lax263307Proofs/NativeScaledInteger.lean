import Lax263307Proofs.NativeSignedArithmetic

namespace Lax263307Proofs.NativeScaledInteger

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational NativeSignedArithmetic

def value (q : ℚ) (D : ℕ) : ℚ := ((q.num*(D/q.den : ℕ) : ℤ) : ℚ)

theorem numerator_value (q : ℚ) (s : ℕ)
    (hv : fractionValue s q.num.natAbs q.den=q) :
    fractionValue s q.num.natAbs 1=(q.num : ℚ) := by
  have hd : (q.den : ℚ)≠0 := by exact_mod_cast q.den_ne_zero
  calc
    _ = fractionValue s q.num.natAbs q.den*(q.den : ℚ) := by
      unfold fractionValue
      split_ifs <;> simp [hd]
    _ = q*(q.den : ℚ) := by rw [hv]
    _ = (q.num : ℚ) := ((div_eq_iff hd).mp q.num_div_den).symm

theorem scaled_value (q : ℚ) (D s : ℕ)
    (hv : fractionValue s q.num.natAbs q.den=q) :
    fractionValue s (q.num.natAbs*(D/q.den)) 1=value q D := by
  have hmul : fractionValue s (q.num.natAbs*(D/q.den)) 1=
      fractionValue s q.num.natAbs 1*(D/q.den : ℕ) := by
    unfold fractionValue
    split_ifs <;> simp [Nat.cast_mul,neg_mul]
  rw [hmul,numerator_value q s hv]
  simp only [value,Int.cast_mul,Int.cast_natCast]

theorem magnitude (q : ℚ) (D : ℕ) : (value q D).num.natAbs=q.num.natAbs*(D/q.den) := by
  simp only [value,Rat.num_intCast,Int.natAbs_mul,Int.natAbs_natCast]

theorem denominator (q : ℚ) (D : ℕ) : (value q D).den=1 := by simp only [value,Rat.den_intCast]

def command : Com := .seq
  (.assign "rat.n" (.mul (.var "rat.n") (.div (.var "cut.denominator") (.var "rat.d"))))
  (.assign "rat.d" (.lit 1))

/-- Clear one denominator using the already computed common product.
The sign is retained; the standard emitter canonicalizes zero. -/
theorem command_spec (B M D : ℕ) (q : ℚ) (h1 : 1<B) (hM : M<B) (hD : D<B)
    (hMD : M*D<B) (hq : Bounded M q) :
    Spec B (fun σ => FractionOutput q σ ∧ σ.vars "cut.denominator"=D) command
      (fun _ τ => FractionOutput (value q D) τ) 8 := by
  rintro σ ⟨h,hDσ⟩
  have hnum : q.num.natAbs*(D/q.den)<B :=
    (Nat.mul_le_mul hq.1 (Nat.div_le_self D q.den)).trans_lt hMD
  have hn := hq.1.trans_lt hM
  have hd := hq.2.trans_lt hM
  have hv : fractionValue (σ.vars "rat.s") q.num.natAbs q.den=q := by
    simpa only [h.2.1,h.2.2.1] using h.1
  have hout := scaled_value q D (σ.vars "rat.s") hv
  have hdiv : D/q.den<B := (Nat.div_le_self _ _).trans_lt hD
  run_vcg
  all_goals simp_all [FractionOutput,magnitude,denominator]

end Lax263307Proofs.NativeScaledInteger
