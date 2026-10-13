import Lax263307.WidthGrowth
import Mathlib.Tactic

namespace Lax263307Proofs.WidthGrowth

open Lax263307.WidthGrowth

/--
---
conclusion: Lax263307.WidthGrowth.order_bound
---
Cancel positive ell from the removed-edge bound. Combine it with the
linear source width inequality to bound t by 12c times W. Raise this to
the a-th power, substitute the class power bound and the host edge bound,
then cancel the positive factor t^(a-1).
-/
theorem order_bound (a A c ℓ t m q : ℕ) (a_positive : 0 < a) (ℓ_positive : 0 < ℓ)
    (t_positive : 0 < t) (W : ℕ → ℕ)
    (W_positive : ∀ M, 1 ≤ W M) (W_power : ∀ M, (W M) ^ a ≤ A * (M + 1) ^ (a - 1))
    (edges : m ≤ 2 * t) (discarded : (24 * c * ℓ) * q ≤ 4 * m * ℓ)
    (width : t ≤ c * (max 1 (6 * W (3 * m * (24 * c * ℓ) ^ 2)) + q)) :
    t ≤ threshold a A c * ℓ ^ (2 * (a - 1)) := by
  let M := 3 * m * (24 * c * ℓ) ^ 2
  have hq : 24 * c * q ≤ 4 * m := by
    apply Nat.le_of_mul_le_mul_right (c := ℓ) _ ℓ_positive
    convert discarded using 1; ring
  have hq' : 3 * c * q ≤ t := by nlinarith
  have hmax : max 1 (6 * W M) = 6 * W M := max_eq_right (by have h := W_positive M; omega)
  have ht : t ≤ 12 * c * W M := by
    change t ≤ c * (max 1 (6 * W M) + q) at width
    rw [hmax] at width
    nlinarith
  have hm : M ≤ 6 * (24 * c) ^ 2 * t * ℓ ^ 2 := by
    calc
      M = (3 * (24 * c) ^ 2 * ℓ ^ 2) * m := by dsimp [M]; ring
      _ ≤ (3 * (24 * c) ^ 2 * ℓ ^ 2) * (2 * t) := Nat.mul_le_mul_left _ edges
      _ = _ := by ring
  have hone : 1 ≤ t * ℓ ^ 2 := Nat.succ_le_of_lt (Nat.mul_pos t_positive (Nat.pow_pos ℓ_positive))
  have hM : M + 1 ≤ (6 * (24 * c) ^ 2 + 1) * t * ℓ ^ 2 := by
    calc
      M + 1 ≤ 6 * (24 * c) ^ 2 * t * ℓ ^ 2 + t * ℓ ^ 2 := Nat.add_le_add hm hone
      _ = _ := by ring
  have hpow : t ^ a ≤ threshold a A c * t ^ (a - 1) * ℓ ^ (2 * (a - 1)) := by
    calc
      t ^ a ≤ (12 * c * W M) ^ a := Nat.pow_le_pow_left ht _
      _ = (12 * c) ^ a * (W M) ^ a := by rw [mul_pow]
      _ ≤ (12 * c) ^ a * (A * (M + 1) ^ (a - 1)) := Nat.mul_le_mul_left _ (W_power M)
      _ ≤ (12 * c) ^ a * (A * ((6 * (24 * c) ^ 2 + 1) * t * ℓ ^ 2) ^ (a - 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left A (Nat.pow_le_pow_left hM _))
      _ = _ := by simp only [mul_pow, ← pow_mul, threshold]; ring
  have heq : t ^ a = t * t ^ (a - 1) := by
    have ha : (a - 1) + 1 = a := Nat.sub_add_cancel (Nat.succ_le_of_lt a_positive)
    calc
      t ^ a = t ^ ((a - 1) + 1) := congrArg (t ^ ·) ha.symm
      _ = _ := by rw [pow_succ, mul_comm]
  have hfinal : t * t ^ (a - 1) ≤ (threshold a A c * ℓ ^ (2 * (a - 1))) * t ^ (a - 1) := by
    calc
      _ = t ^ a := heq.symm
      _ ≤ threshold a A c * t ^ (a - 1) * ℓ ^ (2 * (a - 1)) := hpow
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hfinal (Nat.pow_pos t_positive)


end Lax263307Proofs.WidthGrowth
