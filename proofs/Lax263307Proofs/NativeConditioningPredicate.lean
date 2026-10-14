import Lax263307Proofs.NativeSignedArithmetic

namespace Lax263307Proofs.NativeConditioningPredicate

open Lax455465Proofs.RamRational

def Test (k p D : ℕ) (q e : ℚ) : Prop :=
  0<q ∧ (p : ℚ)*e≤2*(k : ℚ)^2*q^2 ∧ 1/(D : ℚ)≤q

instance (k p D : ℕ) (q e : ℚ) : Decidable (Test k p D q e) :=
  inferInstanceAs (Decidable (0<q ∧ (p : ℚ)*e≤2*(k : ℚ)^2*q^2 ∧ 1/(D : ℚ)≤q))

def Numeric (k p D s n d t m e : ℕ) : Prop :=
  s=0 ∧ 0<n ∧ (t=1 ∨ p*m*d*d≤2*k*k*n*n*e) ∧ d≤D*n

instance (k p D s n d t m e : ℕ) : Decidable (Numeric k p D s n d t m e) :=
  inferInstanceAs (Decidable (s=0 ∧ 0<n ∧ (t=1 ∨ p*m*d*d≤2*k*k*n*n*e) ∧ d≤D*n))

theorem positive (s n d : ℕ) (hs : s≤1) (hd : 0<d) :
    0<fractionValue s n d ↔ s=0 ∧ 0<n := by
  have hdq : (0 : ℚ)<d := by exact_mod_cast hd
  have hnq : (0 : ℚ)≤n := Nat.cast_nonneg n
  have hc : s=0 ∨ s=1 := by omega
  rcases hc with rfl | rfl
  · simp only [fractionValue,show ¬(0 : ℕ)=1 by decide,if_false,true_and]
    rw [div_pos_iff_of_pos_right hdq]
    exact_mod_cast Iff.rfl
  · have hh : -(n : ℚ)/(d : ℚ)≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hdq.le
    simp only [fractionValue,if_true,show ¬(1 : ℕ)=0 by decide,false_and]
    exact iff_false_intro (not_lt_of_ge hh)

theorem numeric_iff (k p D s n d t m e : ℕ) (hs : s≤1) (ht : t≤1)
    (hd : 0<d) (he : 0<e) (hD : 0<D) :
    Numeric k p D s n d t m e ↔ Test k p D (fractionValue s n d) (fractionValue t m e) := by
  have hdq : (0 : ℚ)<d := by exact_mod_cast hd
  have heq : (0 : ℚ)<e := by exact_mod_cast he
  have hDq : (0 : ℚ)<D := by exact_mod_cast hD
  by_cases hs0 : s=0
  · subst s
    have hfloor : 1/(D : ℚ)≤(n : ℚ)/d ↔ d≤D*n := by
      rw [div_le_div_iff₀ hDq hdq]
      norm_cast
      simp [Nat.mul_comm]
    have hedge : (p : ℚ)*fractionValue t m e≤2*(k : ℚ)^2*((n : ℚ)/d)^2 ↔
        t=1 ∨ p*m*d*d≤2*k*k*n*n*e := by
      have hc : t=0 ∨ t=1 := by omega
      rcases hc with rfl | rfl
      · simp only [fractionValue,show ¬(0 : ℕ)=1 by decide,if_false,false_or]
        rw [←mul_div_assoc,div_pow,←mul_div_assoc,div_le_div_iff₀ heq (sq_pos_of_pos hdq)]
        norm_cast
        simp only [pow_two,Nat.mul_assoc]
      · have hl : (p : ℚ)*fractionValue 1 m e≤0 := by
          simp only [fractionValue,if_true]
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg p)
            (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m)) heq.le)
        have hr : (0 : ℚ)≤2*(k : ℚ)^2*((n : ℚ)/d)^2 := by positivity
        simp only [true_or]
        exact iff_true_intro (hl.trans hr)
    simp only [Numeric,Test,positive 0 n d (by decide) hd,show (0 : ℕ)=0 from rfl,true_and]
    rw [show fractionValue 0 n d=(n : ℚ)/d by simp [fractionValue],hedge,hfloor]
  · have hq : ¬0<fractionValue s n d := by rw [positive s n d hs hd]; simp [hs0]
    simp only [Numeric,Test,hs0,hq,false_and]

end Lax263307Proofs.NativeConditioningPredicate
