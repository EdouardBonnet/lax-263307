import Lax263307Proofs.NativeLargeResources

namespace Lax263307Proofs.NativeUniformWordGuards

/-- A numeric intermediate bounded by the word width fits in a word. -/
theorem scalar (v w : ℕ) (h : v≤w) : v<2^w := h.trans_lt Nat.lt_two_pow_self

/-- Reserve two additional bits for an exponential magnitude plus a
numeric offset. This avoids imposing individual intermediate guards. -/
theorem power_add (u v w : ℕ) (hu : u+2≤w) (hv : v+2≤w) : 2^u+v<2^w := by
  have huw : u≤w-1 := by omega
  have hvw : v<w-1 := by omega
  have hp : 2^u≤2^(w-1) := Nat.pow_le_pow_right (by decide) huw
  have hvp : v<2^(w-1) := hvw.trans Nat.lt_two_pow_self
  have he : w=(w-1)+1 := by omega
  rw [he,pow_succ]
  omega

/-- The virtual RAM's multiplication simulation fits with four spare
bits beyond twice the virtual word width. -/
theorem virtual (u w : ℕ) (h : 2*u+4≤w) : 2*(2^u)^2+3<2^w := by
  have hpow : 2^(u*2+4)≤2^w := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_add] at hpow
  norm_num at hpow
  rw [←pow_mul]
  have hp := Nat.two_pow_pos (u*2)
  nlinarith only [hpow,hp]

end Lax263307Proofs.NativeUniformWordGuards
