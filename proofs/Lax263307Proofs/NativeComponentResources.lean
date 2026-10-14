import Lax263307Proofs.NativeComponentTarget
import Lax263307Proofs.NativeUniformWordGuards

namespace Lax263307Proofs.NativeComponentResources

open Lax263307Proofs.NativeSignedArithmetic

def span (n D k : ℕ) : ℕ := n+D+k+20

theorem numeric_bound (n D k M : ℕ) (q : ℚ) (hM : 1≤M) (hq : Bounded M q) :
    NativeComponentTarget.resource n D k q≤20*(span n D k)^2*M := by
  let S := span n D k
  have hS : 1≤S := by dsimp [S,span]; omega
  have hn : n≤S := by dsimp [S,span]; omega
  have hD : D≤S := by dsimp [S,span]; omega
  have hk : k≤S := by dsimp [S,span]; omega
  have h4n : 4*n≤4*S := Nat.mul_le_mul_left 4 hn
  have hnD : 4*n*D≤4*S^2 := by nlinarith only [Nat.mul_le_mul hn hD]
  have hnum : (D-1)*q.num.natAbs≤S*M := Nat.mul_le_mul ((Nat.sub_le D 1).trans hD) hq.1
  have hden : D*q.den≤S*M := Nat.mul_le_mul hD hq.2
  have hleft : 4*n*D*q.num.natAbs≤4*S^2*M := Nat.mul_le_mul hnD hq.1
  have hright : k*q.den≤S*M := Nat.mul_le_mul hk hq.2
  have hp : S≤S^2 := by simpa only [pow_two] using Nat.le_mul_self S
  have hpS : S^2≤S^2*M := Nat.le_mul_of_pos_right _ (by omega)
  have hSM : S*M≤S^2*M := Nat.mul_le_mul_right M hp
  have hSM0 : S≤S^2*M := hp.trans hpS
  have hMM : M≤S^2*M := Nat.le_mul_of_pos_left _ (by positivity)
  have hbase : n+D+k+20=S := rfl
  calc
    NativeComponentTarget.resource n D k q≤S+2*M+4*S+4*S^2+4*S^2*M+4*S*M := by
      dsimp [NativeComponentTarget.resource,NativeComponentTarget.left,NativeComponentTarget.right,
        NativeComponentTarget.numerator,NativeComponentTarget.denominator]
      nlinarith only [hbase,hq.1,hq.2,h4n,hnD,hnum,hden,hleft,hright]
    _≤20*S^2*M := by nlinarith only [hpS,hSM,hSM0,hMM]

/-- The target arithmetic's words need only linear extra bits beyond
the rational cost height and the integer parameter span. -/
theorem word_bound (n D k h w : ℕ) (q : ℚ) (hq : Bounded (2^h) q)
    (hw : h+2*span n D k+6≤w) : NativeComponentTarget.resource n D k q<2^w := by
  let S := span n D k
  have hb := numeric_bound n D k (2^h) q (Nat.one_le_pow _ _ (by decide)) hq
  have hs : S≤2^S := Nat.lt_two_pow_self.le
  have hsq : S^2≤(2^S)^2 := Nat.pow_le_pow_left hs 2
  have hprod : 20*S^2*2^h≤2^5*(2^S)^2*2^h := Nat.mul_le_mul_right _
    (Nat.mul_le_mul (by decide : 20≤2^5) hsq)
  have he : 2^5*(2^S)^2*2^h=2^(h+2*S+5) := by
    rw [← pow_mul,← pow_add,← pow_add]
    congr 1
    omega
  have ht : 2^(h+2*S+5)<2^w := Nat.pow_lt_pow_right (by decide) (by dsimp only [S] at *; omega)
  exact hb.trans_lt ((hprod.trans_eq he).trans_lt ht)

end Lax263307Proofs.NativeComponentResources
