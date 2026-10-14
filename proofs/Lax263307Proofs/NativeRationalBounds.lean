import Lax263307Proofs.NativeSignedArithmetic
import Lax455465Proofs.RamLpRationalRead

namespace Lax263307Proofs.NativeRationalBounds

open Lax455465Proofs.RamRational Lax455465Proofs.RamLpRationalRead
open NativeSignedArithmetic

theorem negate (M : ℕ) (q : ℚ) (hq : Bounded M q) : Bounded M (-q) := by
  simpa only [Bounded,Rat.neg_num,Int.natAbs_neg,Rat.neg_den] using hq

theorem add (M : ℕ) (a b : ℚ) (ha : Bounded M a) (hb : Bounded M b) :
    Bounded (2*M^2) (a+b) := by
  have hs (q : ℚ) : sign q≤1 := by unfold sign; split_ifs <;> omega
  have he := fractionValue_sum (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den
    (hs a) (hs b) a.den_pos b.den_pos
  rw [value_eq,value_eq] at he
  have hn : sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den≤2*M^2 := by
    have hleft := Nat.mul_le_mul ha.1 hb.2
    have hright := Nat.mul_le_mul hb.1 ha.2
    unfold sumNumerator
    split_ifs <;> nlinarith [Nat.sub_le (a.num.natAbs*b.den) (b.num.natAbs*a.den),
      Nat.sub_le (b.num.natAbs*a.den) (a.num.natAbs*b.den)]
  have hd : a.den*b.den≤2*M^2 := by nlinarith [Nat.mul_le_mul ha.2 hb.2]
  have hnd := fractionValue_num_den (sumSign (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den)
    (sumNumerator (sign a) a.num.natAbs a.den (sign b) b.num.natAbs b.den) (a.den*b.den)
    (Nat.mul_pos a.den_pos b.den_pos)
  rw [he] at hnd
  exact ⟨hnd.1.trans_le ((Nat.div_le_self _ _).trans hn),
    hnd.2.trans_le ((Nat.div_le_self _ _).trans hd)⟩

theorem subtract (M : ℕ) (a b : ℚ) (ha : Bounded M a) (hb : Bounded M b) :
    Bounded (2*M^2) (a-b) := by
  simpa only [sub_eq_add_neg] using add M a (-b) ha (negate M b hb)

theorem vector_words (B M n : ℕ) (x : Fin n → ℚ) (h1 : 1<B) (hM : M<B)
    (hx : ∀ i,Bounded M (x i)) :
    ∀ v∈Lax109476.RationalEncoding.encodeVector x,v<B := by
  intro v hv
  simp only [Lax109476.RationalEncoding.encodeVector,List.mem_flatMap,List.mem_ofFn] at hv
  obtain ⟨q,⟨i,rfl⟩,hv⟩ := hv
  simp only [Lax109476.RationalEncoding.encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl
  · split_ifs <;> omega
  · exact (hx i).1.trans_lt hM
  · exact (hx i).2.trans_lt hM

end Lax263307Proofs.NativeRationalBounds
