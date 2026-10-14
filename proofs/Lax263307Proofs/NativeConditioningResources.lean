import Lax263307Proofs.NativeHeavyCandidate

set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeConditioningResources

open Lax263307 RationalConditioning NativeSignedArithmetic

def testBound (k p D M H : ℕ) : ℕ := NativeConditioningTest.resource k p D M M H H

theorem test_le (k p D M H : ℕ) (q e : ℚ) (hq : Bounded M q) (he : Bounded H e) :
    NativeConditioningTest.resource k p D q.num.natAbs q.den e.num.natAbs e.den≤testBound k p D M H := by
  dsimp [testBound,NativeConditioningTest.resource]
  gcongr <;> first | exact hq.1 | exact hq.2 | exact he.1 | exact he.2

theorem test_polynomial (k p D M H R : ℕ) (hk : k≤R) (hp : p≤R) (hD : D≤R)
    (hM : M≤R) (hH : H≤R) (hR : 1≤R) : testBound k p D M H≤32*R^5 := by
  have hmono : testBound k p D M H≤NativeConditioningTest.resource R R R R R R R := by
    dsimp [testBound,NativeConditioningTest.resource]
    gcongr
  have h0 : 1≤R^5 := one_le_pow₀ hR
  have h1 : R≤R^5 := by simpa using (pow_le_pow_right₀ hR (by omega : 1≤5))
  have h2 : R^2≤R^5 := pow_le_pow_right₀ hR (by omega)
  have h3 : R^3≤R^5 := pow_le_pow_right₀ hR (by omega)
  have h4 : R^4≤R^5 := pow_le_pow_right₀ hR (by omega)
  have he : NativeConditioningTest.resource R R R R R R R = 3+9*R+4*R^2+3*R^3+3*R^4+2*R^5 := by
    dsimp [NativeConditioningTest.resource]
    ring
  rw [he] at hmono
  nlinarith

theorem candidate_test (M n r k p : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) (hM : 1≤M) (hA : A.card≤r)
    (hy : ∀ T,Bounded M (y T)) :
    NativeConditioningTest.resource k p (NativeConditioningFloor.base n p^r)
      (rationalValue y A).num.natAbs (rationalValue y A).den
      (edgeNumerator G y A).num.natAbs (edgeNumerator G y A).den≤
      testBound k p (NativeConditioningFloor.base n p^r) M (NativeQuadraticSum.height M n) := by
  apply test_le
  · have hh : A.card≤r+2 := by omega
    simpa only [rationalValue,dif_pos hh] using hy ⟨A,hh⟩
  · exact NativeHeavyCandidate.edge_bounded M n r G y A hM hA hy

end Lax263307Proofs.NativeConditioningResources
