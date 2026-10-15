import Lax263307Proofs.NativeHeavySearch
import Lax263307Proofs.NativeQuadraticResources

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeHeavyResources

open Lax263307 RationalConditioning NativeSignedArithmetic NativeCatalogMetadata

def span (n r k p h : ℕ) : ℕ := n+r+k+p+N n r+h+20

def wordExponent (n r k p h : ℕ) : ℕ := 36*(span n r k p h)^4+10

theorem guards (n r k p h w : ℕ) (hw : wordExponent n r k p h≤w) :
    3*N n r+10<2^w ∧ 3*(n*n)+3*n+r+10<2^w ∧ 2^n<2^w ∧
    2*(2^h)^2+3<2^w ∧ 2*(NativeQuadraticSum.height (2^h) n)^2+3<2^w ∧
    NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
      (2^h) (NativeQuadraticSum.height (2^h) n)<2^w ∧
    NativeConditioningFloor.base n p+NativeConditioningFloor.base n p^r+n+p+r+10<2^w := by
  let S := span n r k p h
  let E := 6*S^4
  let R := 2^E
  have hS : 20≤S := by dsimp [S,span]; omega
  have hn : n+1≤S := by dsimp [S,span]; omega
  have hk : k≤S := by dsimp [S,span]; omega
  have hp : p≤S := by dsimp [S,span]; omega
  have hr : r≤S := by dsimp [S,span]; omega
  have hN : N n r≤S := by dsimp [S,span]; omega
  have hh : h≤S := by dsimp [S,span]; omega
  have hS2 : S≤S^2 := by nlinarith only [hS]
  have hS3 : S^2≤S^3 := pow_le_pow_right₀ (by omega : 1≤S) (by omega)
  have hS4 : S^3≤S^4 := pow_le_pow_right₀ (by omega : 1≤S) (by omega)
  have hSE : S≤E := by dsimp [E]; omega
  have hER : E≤R := (Nat.lt_two_pow_self).le
  have hSR : S≤R := hSE.trans hER
  have hR : 1≤R := one_le_pow₀ (by decide : 1≤(2:ℕ))
  have hR2 : R≤R^2 := by nlinarith only [hR]
  have hR5 : R^2≤R^5 := pow_le_pow_right₀ hR (by omega)
  have hMR : 2^h≤R := Nat.pow_le_pow_right (by decide) (hh.trans hSE)
  have hheight : (2*h+1)*(n*n+1)≤E := by
    have ht : (2*h+1)*(n*n+1)≤(2*S+1)*(S*S+1) := by gcongr <;> omega
    dsimp [E]
    nlinarith only [ht,hS,hS4,Nat.zero_le (S^2)]
  have hHR : NativeQuadraticSum.height (2^h) n≤R := by
    rw [NativeQuadraticResources.height_bits]
    exact Nat.pow_le_pow_right (by decide) hheight
  have hbase : NativeConditioningFloor.base n p≤2*S^3 := by
    have hlog : Nat.log2 n+1≤S := (Nat.add_le_add_right (Nat.log2_le_self n) 1).trans hn
    dsimp [NativeConditioningFloor.base]
    calc
      2*n*p*(Nat.log2 n+1)≤2*S*S*S := by gcongr <;> omega
      _ = 2*S^3 := by ring
  have hbaseE : NativeConditioningFloor.base n p≤E := by dsimp [E]; omega
  have hDR : NativeConditioningFloor.base n p^r≤R := by
    calc
      NativeConditioningFloor.base n p^r≤(2^(2*S^3))^r :=
        Nat.pow_le_pow_left (hbase.trans (Nat.lt_two_pow_self).le) r
      _ = 2^((2*S^3)*r) := (pow_mul _ _ _).symm
      _ ≤ 2^E := Nat.pow_le_pow_right (by decide) (by dsimp [E]; nlinarith only [Nat.mul_le_mul_left (2*S^3) hr,Nat.zero_le (S^4)])
  have hcommon : 128*R^5<2^w := by
    have heq : 128*R^5=2^(5*E+7) := by
      dsimp [R]
      rw [←pow_mul,pow_add]
      norm_num
      rw [Nat.mul_comm E 5,Nat.mul_comm]
    rw [heq]
    apply Nat.pow_lt_pow_right (by decide)
    change 36*S^4+10≤w at hw
    dsimp [E]
    omega
  have hkR := hk.trans hSR
  have hpR := hp.trans hSR
  have hnR : n≤R := (by omega : n≤S).trans hSR
  have hrR := hr.trans hSR
  have hNR := hN.trans hSR
  have hbaseR := hbaseE.trans hER
  have hM2 : (2^h)^2≤R^2 := Nat.pow_le_pow_left hMR 2
  have hH2 : (NativeQuadraticSum.height (2^h) n)^2≤R^2 := Nat.pow_le_pow_left hHR 2
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact lt_of_le_of_lt (by omega) hcommon
  · exact lt_of_le_of_lt (by nlinarith only [Nat.mul_le_mul hnR hnR,hnR,hrR,hR,hR2,hR5]) hcommon
  · exact (Nat.pow_le_pow_right (by decide) ((by omega : n≤S).trans hSE)).trans_lt
      (lt_of_le_of_lt (by omega : R≤128*R^5) hcommon)
  · exact lt_of_le_of_lt (by omega) hcommon
  · exact lt_of_le_of_lt (by omega) hcommon
  · exact (NativeConditioningResources.test_polynomial k p (NativeConditioningFloor.base n p^r)
      (2^h) (NativeQuadraticSum.height (2^h) n) R hkR hpR hDR hMR hHR hR).trans_lt
      (lt_of_le_of_lt (by omega) hcommon)
  · exact lt_of_le_of_lt (by omega) hcommon

/-- Polynomial source cost in the catalog size and original moment bit height. -/
theorem cost_bound (n r h : ℕ) : NativeHeavySearch.cost (2^h) n r≤
    2000*(n+r+N n r+h+20)^6 := by
  let S := n+r+N n r+h+20
  have hS : 20≤S := by dsimp [S]; omega
  have hn : n+1≤S := by dsimp [S]; omega
  have hN : N n r≤S := by dsimp [S]; omega
  have hr : r≤S := by dsimp [S]; omega
  have hh : h+1≤S := by dsimp [S]; omega
  have hs : n.size≤S := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega : n≤S)
  have hq : NativeQuadraticSum.cost (2^h) n≤1000*S^5 := by
    apply (NativeQuadraticResources.cost_bound n h).trans
    calc
      1000*(h+1)*(n+1)^4≤1000*S*S^4 := by gcongr
      _ = 1000*S^5 := by ring
  have hsize : ((2^h)^2).size≤2*S+1 := by
    rw [NativeQuadraticResources.square_power,Nat.size_pow]
    omega
  have hS2 : S≤S^2 := by nlinarith only [hS]
  have hS25 : S^2≤S^5 := pow_le_pow_right₀ (by omega : 1≤S) (by omega)
  have hc : NativeConditioningEntry.cost (2^h) n r+18≤1500*S^5 := by
    dsimp [NativeConditioningEntry.cost,NativeHeavyCandidate.cost,NativeConditioningNumerator.cost]
    have hx : (17*N n r+120)*n≤(17*S+120)*S := by gcongr <;> omega
    nlinarith only [hx,hN,hq,hS2,hS25,hS]
  have hx : (NativeConditioningEntry.cost (2^h) n r+18)*N n r≤1500*S^6 := by
    calc
      _ ≤ (1500*S^5)*S := Nat.mul_le_mul hc hN
      _ = 1500*S^6 := by ring
  have hS56 : S^5≤S^6 := pow_le_pow_right₀ (by omega : 1≤S) (by omega)
  change NativeHeavySearch.cost (2^h) n r≤2000*S^6
  dsimp [NativeHeavySearch.cost]
  omega


end Lax263307Proofs.NativeHeavyResources
