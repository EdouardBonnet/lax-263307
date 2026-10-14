import Lax263307Proofs.NativeRationalBounds

namespace Lax263307Proofs.NativeSumHeight

open Lax455465Proofs.RamRational Lax455465Proofs.RamLpRationalRead
open NativeSignedArithmetic

theorem weaken {A B : ℕ} {q : ℚ} (h : A≤B) (hq : Bounded A q) : Bounded B q :=
  ⟨hq.1.trans h,hq.2.trans h⟩

/-- Distinct input bounds make the height recurrence multiplicative,
rather than repeatedly squaring the bound of the accumulated sum. -/
theorem add (A C : ℕ) (a b : ℚ) (ha : Bounded A a) (hb : Bounded C b) :
    Bounded (2*A*C) (a+b) := by
  have hs (q : ℚ) : sign q≤1 := by unfold sign; split_ifs <;> omega
  have he := fractionValue_sum (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den
    (hs a) (hs b) a.den_pos b.den_pos
  rw [value_eq,value_eq] at he
  have hn : sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den≤2*A*C := by
    have hleft := Nat.mul_le_mul ha.1 hb.2
    have hright := Nat.mul_le_mul hb.1 ha.2
    unfold sumNumerator
    split_ifs <;> nlinarith [Nat.sub_le (a.num.natAbs*b.den) (b.num.natAbs*a.den),
      Nat.sub_le (b.num.natAbs*a.den) (a.num.natAbs*b.den)]
  have hd : a.den*b.den≤2*A*C := by nlinarith [Nat.mul_le_mul ha.2 hb.2]
  have hnd := fractionValue_num_den (sumSign (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den)
    (sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den) (a.den*b.den)
    (Nat.mul_pos a.den_pos b.den_pos)
  rw [he] at hnd
  exact ⟨hnd.1.trans_le ((Nat.div_le_self _ _).trans hn),
    hnd.2.trans_le ((Nat.div_le_self _ _).trans hd)⟩

theorem multiply (A C : ℕ) (a b : ℚ) (ha : Bounded A a) (hb : Bounded C b) :
    Bounded (A*C) (a*b) := by
  have hprod (s t u v d e : ℕ) (hs : s≤1) (ht : t≤1) :
      fractionValue (if s=t then 0 else 1) (u*v) (d*e)=fractionValue s u d*fractionValue t v e := by
    have hs' : s=0 ∨ s=1 := by omega
    have ht' : t=0 ∨ t=1 := by omega
    rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl <;>
      norm_num [fractionValue,Nat.cast_mul] <;> ring
  have hs (q : ℚ) : sign q≤1 := by unfold sign; split_ifs <;> omega
  have he := hprod (sign a) (sign b) a.num.natAbs b.num.natAbs a.den b.den (hs a) (hs b)
  rw [value_eq,value_eq] at he
  have hnd := fractionValue_num_den (if sign a=sign b then 0 else 1)
    (a.num.natAbs*b.num.natAbs) (a.den*b.den) (Nat.mul_pos a.den_pos b.den_pos)
  rw [he] at hnd
  exact ⟨hnd.1.trans_le ((Nat.div_le_self _ _).trans (Nat.mul_le_mul ha.1 hb.1)),
    hnd.2.trans_le ((Nat.div_le_self _ _).trans (Nat.mul_le_mul ha.2 hb.2))⟩

theorem sum (M : ℕ) (xs : List ℚ) (hx : ∀ x∈xs,Bounded M x) :
    Bounded ((2*M)^xs.length) xs.sum := by
  induction xs with
  | nil => simp [Bounded]
  | cons x xs ih =>
    have hh := add M ((2*M)^xs.length) x xs.sum (hx x (by simp))
      (ih (fun y hy => hx y (by simp [hy])))
    simpa only [List.sum_cons,List.length_cons,pow_succ,Nat.mul_comm,Nat.mul_assoc] using hh

theorem sum_bits (h : ℕ) (xs : List ℚ) (hx : ∀ x∈xs,Bounded (2^h) x) :
    Bounded (2^((h+1)*xs.length)) xs.sum := by
  have hh : (2*(2^h))^xs.length=2^((h+1)*xs.length) := by
    rw [pow_mul,pow_succ]
    congr 1
    exact Nat.mul_comm _ _
  simpa only [hh] using sum (2^h) xs hx

theorem uniform_entry (M : ℕ) (xs : List ℚ) (hM : 1≤M) (hx : ∀ x∈xs,Bounded M x)
    (x : ℚ) (hmem : x∈xs) : Bounded ((2*M)^(xs.length+1)) x := by
  apply weaken _ (hx x hmem)
  calc
    M ≤ 2*M := by omega
    _ = (2*M)^1 := (pow_one _).symm
    _ ≤ (2*M)^(xs.length+1) := Nat.pow_le_pow_right (by omega) (by omega)

theorem uniform_partial (M : ℕ) (xs : List ℚ) (hM : 1≤M) (hx : ∀ x∈xs,Bounded M x)
    (i : ℕ) : Bounded ((2*M)^(xs.length+1)) (xs.take i).sum := by
  apply weaken _ (sum M (xs.take i) (fun x h => hx x (List.mem_of_mem_take h)))
  apply Nat.pow_le_pow_right (by omega)
  simp only [List.length_take]
  omega

end Lax263307Proofs.NativeSumHeight
