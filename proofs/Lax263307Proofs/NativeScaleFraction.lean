import Lax263307Proofs.NativeSignedArithmetic
import Lax455465Proofs.RamLpRationalRead

namespace Lax263307Proofs.NativeScaleFraction

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational Lax455465Proofs.RamArithmetic
open NativeSignedArithmetic

theorem value (sign n d s : ℕ) : fractionValue sign (n*s) d=fractionValue sign n d*(s : ℚ) := by
  unfold fractionValue
  split_ifs <;> push_cast <;> ring

theorem bounds (M s : ℕ) (q : ℚ) (hs : s≤M) (hq : Bounded M q) :
    Bounded (M^2) (q*(s : ℚ)) := by
  have hM : 1≤M := q.den_pos.trans_le hq.2
  let sign := RamLpRationalRead.sign q
  have hv : fractionValue sign q.num.natAbs q.den=q := RamLpRationalRead.value_eq q
  have he : fractionValue sign (q.num.natAbs*s) q.den=q*(s : ℚ) := by rw [value,hv]
  obtain ⟨hn,hd⟩ := fractionValue_num_den sign (q.num.natAbs*s) q.den q.den_pos
  rw [he] at hn hd
  constructor
  · rw [hn]
    exact (Nat.div_le_self _ _).trans (by simpa only [pow_two] using Nat.mul_le_mul hq.1 hs)
  · rw [hd]
    exact (Nat.div_le_self _ _).trans (hq.2.trans (by nlinarith only [hM]))

def command : Com := .seq (.assign "rat.n" (.mul (.var "rat.n") (.var "scale.value"))) normalizeFraction

/-- Multiply a canonical signed rational by a computed natural scale
and reduce it again, preserving its sign and exact rational value. -/
theorem command_spec (B M s : ℕ) (q : ℚ) (hB : 2*M^2+3<B) (hs : s≤M) (hq : Bounded M q) :
    Spec B (fun σ => FractionOutput q σ ∧ σ.vars "scale.value"=s) command
      (fun _ τ => FractionOutput (q*(s : ℚ)) τ) (36*M.size+20) := by
  have hMpos : 1≤M := q.den_pos.trans_le hq.2
  have hM : M<B := by nlinarith only [hB,hMpos]
  have hprod : q.num.natAbs*s≤M^2 := by simpa only [pow_two] using Nat.mul_le_mul hq.1 hs
  have hnum : q.num.natAbs*s<B := hprod.trans_lt (by omega : M^2<B)
  rintro σ ⟨hqσ,hsσ⟩
  let ν := σ.setVar "rat.n" (q.num.natAbs*s)
  have r1 : Run B (.assign "rat.n" (.mul (.var "rat.n") (.var "scale.value"))) σ ν 4 := Run.assign
    (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hqσ.2.1.symm,hqσ.2.1 ▸ hq.1.trans_lt hM⟩)
      (by rw [evalB_var_iff]; exact ⟨hsσ.symm,hsσ ▸ hs.trans_lt hM⟩) hnum)
  obtain ⟨τ,r2,p2⟩ := normalizeFraction_output_spec B (σ.vars "rat.s") (q.num.natAbs*s) q.den
    hqσ.2.2.2 hnum (hq.2.trans_lt hM) q.den_pos ν
    ⟨by rfl,(r1.frame_var "rat.d" (by decide)).trans hqσ.2.2.1,
      r1.frame_var "rat.s" (by decide)⟩
  have he : fractionValue (σ.vars "rat.s") (q.num.natAbs*s) q.den=q*(s : ℚ) := by
    rw [value]
    have hv : fractionValue (σ.vars "rat.s") q.num.natAbs q.den=q := by
      simpa only [hqσ.2.1,hqσ.2.2.1] using hqσ.1
    rw [hv]
  exact ⟨τ,(r1.seq r2).mono (by have hsize := Nat.size_le_size hq.2; omega),by simpa only [he] using p2⟩

end Lax263307Proofs.NativeScaleFraction
