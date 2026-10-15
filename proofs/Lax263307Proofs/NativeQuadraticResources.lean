import Lax263307Proofs.NativeQuadraticSum

namespace Lax263307Proofs.NativeQuadraticResources

open NativeQuadraticSum

theorem square_power (h : ℕ) : (2^h)^2=2^(2*h) := by
  rw [←pow_mul,Nat.mul_comm h 2]

theorem height_bits (n h : ℕ) : height (2^h) n=2^((2*h+1)*(n*n+1)) := by
  rw [height,square_power]
  have he : 2*2^(2*h)=2^(2*h+1) := by rw [pow_add,pow_one]; exact Nat.mul_comm _ _
  rw [he,←pow_mul]

/-- The complete native edge-sum cost is polynomial in the original
vertex count and the input bit height, even for signed rationals. -/
theorem cost_bound (n h : ℕ) : cost (2^h) n≤1000*(h+1)*(n+1)^4 := by
  simp only [cost,height_bits,square_power,Nat.size_pow]
  nlinarith only [Nat.zero_le (h*n),Nat.zero_le (h*n^2),Nat.zero_le (h*n^3),
    Nat.zero_le (h*n^4),Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4)]

def wordExponent (n h : ℕ) : ℕ := 2*((2*h+1)*(n*n+1))+10


end Lax263307Proofs.NativeQuadraticResources
