import Lax263307Proofs.NativeSumHeight
import Lax455465Proofs.RamFractionPrimitives

set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativePositiveQuotient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational
open NativeSignedArithmetic

theorem inverse_bounded (M : ℕ) (q : ℚ) (hM : 1≤M) (hq : Bounded M q) : Bounded M q⁻¹ := by
  constructor
  · simp only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast]
    have hs : q.num.sign.natAbs≤1 := by
      rcases lt_trichotomy q.num 0 with h | h | h
      · simp [Int.sign_eq_neg_one_of_neg h]
      · simp [h]
      · simp [Int.sign_eq_one_of_pos h]
    exact (Nat.mul_le_mul_right q.den hs).trans (by simpa using hq.2)
  · rw [Rat.den_inv]
    split_ifs <;> first | exact hM | exact hq.1

theorem inverse_spec (B M : ℕ) (q : ℚ) (hB : M+2<B) (hq : Bounded M q) :
    Spec B (Stored "left" q) invertFraction (fun _ τ => FractionOutput q⁻¹ τ) (36*M.size+40) := by
  intro σ h
  have hh := h
  simp only [Stored,String.reduceAppend] at hh
  obtain ⟨τ,rr,ht⟩ := invertFraction_spec B (σ.vars "left.s") q.num.natAbs q.den (by omega)
    hh.2.2.2 (hq.1.trans_lt (by omega)) (hq.2.trans_lt (by omega)) σ ⟨rfl,hh.2.1,hh.2.2.1⟩
  have he : fractionValue (σ.vars "left.s") q.num.natAbs q.den=q := by
    simpa only [←hh.2.1,←hh.2.2.1] using hh.1
  exact ⟨τ,rr.mono (by have hsize := Nat.size_le_size hq.1; omega),by simpa only [he] using ht⟩

def positive : Com := .ite (.eq (.var "rat.s") (.lit 1)) RamFractionPrimitives.zero .skip

theorem positive_spec (B M : ℕ) (q : ℚ) (hB : M+2<B) (hq : Bounded M q) :
    Spec B (FractionOutput q) positive (fun _ τ => FractionOutput (max 0 q) τ) 10 := by
  intro σ h
  have hsign := h.2.2.2
  by_cases hs : σ.vars "rat.s"=1
  · have hq0 : q≤0 := by
      rw [←h.1]
      simp only [fractionValue,hs,if_true]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    obtain ⟨τ,rr,ht⟩ := RamFractionPrimitives.zero_spec B (by omega) σ trivial
    have hc : (Cond.eq (.var "rat.s") (.lit 1)).evalB B σ=some true := by
      rw [evalB_condEq (evalB_var (hs ▸ (by omega : 1<B))) (evalB_lit (by omega : 1<B)),hs]
      rfl
    exact ⟨τ,(Run.ite_true (d:=.skip) hc rr).mono (by decide),by simpa only [max_eq_left hq0] using ht⟩
  · have hq0 : 0≤q := by
      rw [←h.1]
      simp only [fractionValue,hs,if_false]
      positivity
    have hc : (Cond.eq (.var "rat.s") (.lit 1)).evalB B σ=some false := by
      rw [evalB_condEq (evalB_var (hsign.trans_lt (by omega : 1<B))) (evalB_lit (by omega : 1<B))]
      simp [hs]
    exact ⟨σ,(Run.ite_false (c:=RamFractionPrimitives.zero) hc Run.skip).mono (by decide),
      by simpa only [max_eq_right hq0] using h⟩

theorem positive_bounded (M : ℕ) (q : ℚ) (hM : 1≤M) (hq : Bounded M q) :
    Bounded M (max 0 q) := by
  rcases le_total q 0 with h | h
  · simp only [max_eq_left h]
    exact ⟨by simp,by simpa using hM⟩
  · simpa only [max_eq_right h] using hq

def command : Com := .seq (load "quotient.denominator")
  (.seq (save "left") (.seq invertFraction (.seq (save "right")
    (.seq (load "quotient.numerator") (.seq (save "left") (.seq multiplyFraction positive))))))

theorem command_spec (B M : ℕ) (a b : ℚ) (hM : 1≤M) (hB : 2*M^2+3<B)
    (ha : Bounded M a) (hb : Bounded M b) :
    Spec B (fun σ => Stored "quotient.numerator" a σ ∧ Stored "quotient.denominator" b σ)
      command (fun _ τ => FractionOutput (max 0 (a/b)) τ) (72*(M^2).size+144) := by
  have hsmall : M+2<B := by nlinarith
  have h1 : 1<B := by nlinarith
  have hMB : M<B := by omega
  have hbi := inverse_bounded M b hM hb
  rintro σ ⟨haσ,hbσ⟩
  obtain ⟨σ1,r1,p1⟩ := load_spec B "quotient.denominator" b h1 (hb.1.trans_lt hMB) (hb.2.trans_lt hMB) (by decide) σ hbσ
  obtain ⟨σ2,r2,p2⟩ := save_spec B "left" b h1 (hb.1.trans_lt hMB) (hb.2.trans_lt hMB) (by decide) σ1 p1
  obtain ⟨σ3,r3,p3⟩ := inverse_spec B M b hsmall hb σ2 p2
  obtain ⟨σ4,r4,p4⟩ := save_spec B "right" b⁻¹ h1 (hbi.1.trans_lt hMB) (hbi.2.trans_lt hMB) (by decide) σ3 p3
  have ha4 : Stored "quotient.numerator" a σ4 := by
    have rr := r1.seq (r2.seq (r3.seq r4))
    simpa only [Stored,String.reduceAppend,rr.frame_var "quotient.numerator.s" (by decide),
      rr.frame_var "quotient.numerator.n" (by decide),rr.frame_var "quotient.numerator.d" (by decide)] using haσ
  obtain ⟨σ5,r5,p5⟩ := load_spec B "quotient.numerator" a h1 (ha.1.trans_lt hMB) (ha.2.trans_lt hMB) (by decide) σ4 ha4
  obtain ⟨σ6,r6,p6⟩ := save_spec B "left" a h1 (ha.1.trans_lt hMB) (ha.2.trans_lt hMB) (by decide) σ5 p5
  have hb6 : Stored "right" b⁻¹ σ6 := by
    simpa only [Stored,String.reduceAppend,(r5.seq r6).frame_var "right.s" (by decide),
      (r5.seq r6).frame_var "right.n" (by decide),(r5.seq r6).frame_var "right.d" (by decide)] using p4
  obtain ⟨σ7,r7,p7⟩ := multiply_spec B M a b⁻¹ hB ha hbi σ6 ⟨p6,hb6⟩
  have hab : Bounded (M^2) (a*b⁻¹) := by simpa only [pow_two] using NativeSumHeight.multiply M M a b⁻¹ ha hbi
  obtain ⟨τ,r8,p8⟩ := positive_spec B (M^2) (a*b⁻¹) (by nlinarith) hab σ7 p7
  have hsize : (a.den*(b⁻¹).den).size≤(M^2).size := Nat.size_le_size (by nlinarith [Nat.mul_le_mul ha.2 hbi.2])
  have hsizeM : M.size≤(M^2).size := Nat.size_le_size (by nlinarith)
  exact ⟨τ,(r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq r8))))))).mono (by omega),
    by simpa only [div_eq_mul_inv] using p8⟩

theorem height (M : ℕ) (a b : ℚ) (hM : 1≤M) (ha : Bounded M a) (hb : Bounded M b) :
    Bounded (M^2) (max 0 (a/b)) := by
  apply positive_bounded (M^2) (a/b) (by nlinarith)
  simpa only [div_eq_mul_inv,pow_two] using NativeSumHeight.multiply M M a b⁻¹ ha (inverse_bounded M b hM hb)

end Lax263307Proofs.NativePositiveQuotient
