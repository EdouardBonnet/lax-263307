import Lax263307Proofs.NativeNodePrecision
import Lax263307Proofs.NativeMomentFamily

namespace Lax263307Proofs.NativePrecisionResources

open Lax263307 AlgorithmParameters ParameterResources
open NativeNodePrecision

/-- All intermediate scalar guards for protected-radius computation
are polynomial in a bound for the actual algorithm parameters. -/
theorem guard_bound (n D N b r S : ℕ) (hn : 0<n) (hD : 0<D) (hN : 0<N) (hb : 0<b)
    (hnS : n≤S) (hDS : D≤S) (hNS : N≤S) (hrS : r≤S) (hbS : b≤2*S^2)
    (hR : radius n D N b r≤S) (hP : prec n D N b r≤S) (hI : count n D N b r≤S) :
    NativeNodePrecision.guard n D N b r≤400*(S+1)^2 := by
  have hpow : 0<b^r := pow_pos hb _
  have hF : 0<256*N*n*n*D*D := by positivity
  have hp : b^r≤S := (Nat.le_mul_of_pos_left _ hF).trans hR
  have h5 : 256*N*n*n*D*D≤S := (Nat.le_mul_of_pos_right _ hpow).trans hR
  have h4 : 256*N*n*n*D≤S := (Nat.le_mul_of_pos_right _ hD).trans h5
  have h3 : 256*N*n*n≤S := (Nat.le_mul_of_pos_right _ hD).trans h4
  have h2 : 256*N*n≤S := (Nat.le_mul_of_pos_right _ hn).trans h3
  have h1 : 256*N≤S := (Nat.le_mul_of_pos_right _ hn).trans h2
  have hprod : prec n D N b r*N≤S^2 := by simpa only [pow_two] using Nat.mul_le_mul hP hNS
  dsimp only [NativeNodePrecision.guard]
  nlinarith only [hnS,hDS,hNS,hrS,hbS,hR,hP,hI,hp,h5,h4,h3,h2,h1,hprod]

/-- In particular, the native precision setup's actual guard is a
fixed polynomial in the common quasipolynomial parameter resource. -/
theorem actual_guard (a K b n D : ℕ) (hK : 0<K) (hn : 0<n) (hD : 0<D) :
    NativeNodePrecision.guard n D (MomentLP.dimension n (level a K b n D)) (floorDenominator a K b n D)
      (level a K b n D)≤400*(resource a K b n D+1)^2 := by
  let S := resource a K b n D
  have hnS : n≤S := by dsimp [S,resource]; omega
  have hDS : D≤S := by dsimp [S,resource]; omega
  have hNS : MomentLP.dimension n (level a K b n D)≤S := by dsimp [S,resource]; omega
  have hrS : level a K b n D≤S := by dsimp [S,resource]; omega
  have hR : radiusDenominator a K b n D≤S := by dsimp [S,resource]; omega
  have hP : precision a K b n D≤S := by dsimp [S,resource]; omega
  have hI : iterations a K b n D≤S := by dsimp [S,resource]; omega
  have hf : 0<floorDenominator a K b n D := by
    unfold floorDenominator sparsity targetThreshold
    positivity
  have hbS : floorDenominator a K b n D≤2*S^2 := by
    rw [NativeNodeParameters.floor_eq]
    have hm := Nat.mul_le_mul hnS hrS
    nlinarith only [hm]
  exact guard_bound n D _ _ _ S hn hD (NativeMomentFamily.dimension_positive _ _) hf
    hnS hDS hNS hrS hbS
    (by simpa only [actual_radius] using hR)
    (by simpa only [actual_precision] using hP)
    (by simpa only [actual_iterations] using hI)

end Lax263307Proofs.NativePrecisionResources
