import Lax263307Proofs.NativeLargeCapacity

namespace Lax263307Proofs.NativeLargeResources

open Lax263307 ComputedSeparators NativeSignedArithmetic NativeLargeCapacity

/-- The ceiling of a nonnegative integral numerator divided by a
positive integral denominator is no larger than the numerator. -/
theorem value_le (b n r load k : ℕ) (hn : 0<n) (hl : 0<load) :
    value b n r load k≤numerator b n r k+1 := by
  have hd : 0<denominator n load := by dsimp [denominator]; positivity
  have hm : numerator b n r k≤numerator b n r k*denominator n load :=
    Nat.le_mul_of_pos_right _ hd
  have hp : (numerator b n r k+denominator n load-1)+1=numerator b n r k+denominator n load := by omega
  have hdiv : (numerator b n r k+denominator n load-1)/denominator n load<numerator b n r k+1 := by
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    nlinarith only [hp,hm]
  dsimp [value]
  omega

theorem numerator_mono (b n r s k : ℕ) (h : r≤s) : numerator b n r k≤numerator b n s k := by
  dsimp [numerator]
  gcongr

theorem resource_mono (b n r s load k : ℕ) (h : r≤s) : resource b n r load k≤resource b n s load k := by
  dsimp [resource,numerator]
  gcongr

def heightExponent (b n load k h : ℕ) : ℕ :=
  h+numerator b n n k+resource b n n load k+n+30

theorem capacity_height (b n load k h : ℕ) (R : Finset (Fin n)) (hn : 0<n) (hl : 0<load) :
    Bounded (2^heightExponent b n load k h) (largeCapacity b n R.card load k : ℚ) := by
  have hr := NativeMaskUnpack.card_bound R
  have hv : value b n R.card load k≤heightExponent b n load k h := by
    have hh := (value_le b n R.card load k hn hl).trans (Nat.add_le_add_right (numerator_mono b n R.card n k hr) 1)
    dsimp [heightExponent]
    omega
  rw [exact_value b n R.card load k hn hl]
  refine ⟨?_,?_⟩
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using hv.trans (Nat.lt_two_pow_self).le
  · simpa only [Rat.den_natCast] using (Nat.one_le_two_pow : 1≤2^heightExponent b n load k h)

theorem input_height (b n load k h : ℕ) (q : ℚ) (hq : Bounded (2^h) q) :
    Bounded (2^heightExponent b n load k h) q := by
  have hh : h≤heightExponent b n load k h := by dsimp [heightExponent]; omega
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hh
  exact ⟨hq.1.trans hp,hq.2.trans hp⟩

theorem resource_le_height (b n load k h : ℕ) (R : Finset (Fin n)) :
    resource b n R.card load k≤heightExponent b n load k h := by
  have hh := resource_mono b n R.card n load k (NativeMaskUnpack.card_bound R)
  dsimp [heightExponent]
  omega

end Lax263307Proofs.NativeLargeResources
