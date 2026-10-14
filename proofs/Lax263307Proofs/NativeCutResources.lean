import Lax263307Proofs.NativeClearNormal

namespace Lax263307Proofs.NativeCutResources

open Lax263307.RationalCutBuffer NativeSignedArithmetic

def wordExponent (n h : ℕ) : ℕ := (n+1)*(h+1)+10

theorem product_bound (n h : ℕ) (a : Fin n → ℚ) (ha : ∀ i,Bounded (2^h) (a i)) :
    denominator a≤2^(n*h) := by
  have hh (s : Finset (Fin n)) : (∏ i∈s,(a i).den)≤2^(s.card*h) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.add_mul,pow_add]
      simpa only [Nat.one_mul,Nat.mul_one,Nat.mul_comm] using Nat.mul_le_mul (ha i).2 ih
  simpa only [Finset.card_univ,Fintype.card_fin,denominator] using hh Finset.univ

/-- Denominator clearing needs only linearly many input-height bits, even
though the numerical product itself can be exponentially large. -/
theorem guard_bound (n h : ℕ) (a : Fin n → ℚ) (ha : ∀ i,Bounded (2^h) (a i)) :
    2^h*denominator a+2^h+denominator a+3*n+10<2^(wordExponent n h) := by
  let E := (n+1)*(h+1)
  have hD := product_bound n h a ha
  have hE : n*h≤E := by dsimp [E]; nlinarith
  have hH : h≤E := by dsimp [E]; nlinarith
  have hboth : h+n*h≤E := by dsimp [E]; nlinarith
  have hnE : n≤E := by dsimp [E]; nlinarith
  have hpD : denominator a≤2^E := hD.trans (Nat.pow_le_pow_right (by decide) hE)
  have hpH : 2^h≤2^E := Nat.pow_le_pow_right (by decide) hH
  have hpM : 2^h*denominator a≤2^E := by
    calc
      _ ≤ 2^h*2^(n*h) := Nat.mul_le_mul_left _ hD
      _ = 2^(h+n*h) := (pow_add _ _ _).symm
      _ ≤ 2^E := Nat.pow_le_pow_right (by decide) hboth
  have hnU : n<2^E := hnE.trans_lt Nat.lt_two_pow_self
  have hU := Nat.two_pow_pos E
  change _<2^(E+10)
  rw [pow_add]
  norm_num
  omega

theorem integer_height (n h : ℕ) (a : Fin n → ℚ) (ha : ∀ i,Bounded (2^h) (a i)) (i : Fin n) :
    (integerNormal a i).natAbs≤2^((n+1)*h) := by
  have hD := product_bound n h a ha
  have hi : (integerNormal a i).natAbs≤2^h*denominator a := by
    simp only [integerNormal,Int.natAbs_mul,Int.natAbs_natCast]
    exact Nat.mul_le_mul (ha i).1 (Nat.div_le_self _ _)
  calc
    _ ≤ 2^h*denominator a := hi
    _ ≤ 2^h*2^(n*h) := Nat.mul_le_mul_left _ hD
    _ = 2^((n+1)*h) := by rw [←pow_add]; congr 1; ring

end Lax263307Proofs.NativeCutResources
