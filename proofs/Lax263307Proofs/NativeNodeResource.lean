import Lax263307Proofs.NativeNodeParameters

namespace Lax263307Proofs.NativeNodeResource

open Lax263307 AlgorithmParameters ParameterResources

/-- The scalar guards used while loading actual node parameters are
polynomial in the already checked common parameter resource. -/
theorem guard_bound (a K b n D : ℕ) (hK : 0<K) (hn : 0<n) :
    NativeNodeParameters.guard a K b n D≤
      (a+K+24*b+(4*a+2)+50)*(resource a K b n D+1)^2 := by
  let R := resource a K b n D
  have hnR : n≤R := by dsimp [R,resource]; omega
  have hDR : D≤R := by dsimp [R,resource]; omega
  have hload : load b n D≤R := by dsimp [R,resource]; omega
  have hsp : sparsity a K b n D≤R := by dsimp [R,resource]; omega
  have hl : level a K b n D≤R := by dsimp [R,resource]; omega
  have hth : targetThreshold a K b n D≤R := by
    have ht : targetThreshold a K b n D≤sparsity a K b n D := by unfold sparsity; omega
    exact ht.trans hsp
  have hp : (load b n D+1)^(4*a+2)≤R := by
    have hh : (load b n D+1)^(4*a+2)≤targetThreshold a K b n D :=
      Nat.le_mul_of_pos_left _ hK
    exact hh.trans hth
  have hlog : Nat.log2 n+1≤n := by
    rw [←NativeLogarithms.size_eq n hn]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hL : logarithm n≤2*n := by
    change Nat.log2 (2*n)+1≤2*n
    rw [←NativeLogarithms.size_eq (2*n) (by omega)]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hf : floorDenominator a K b n D≤2*R^2 := by
    rw [NativeNodeParameters.floor_eq]
    have hm := Nat.mul_le_mul hnR hl
    nlinarith only [hm]
  have hmul : 12*b*D≤12*b*R := Nat.mul_le_mul_left _ hDR
  have hR : 1≤R+1 := by omega
  have hRs : R≤(R+1)^2 := by nlinarith only [hR]
  dsimp only [NativeNodeParameters.guard]
  change _≤(a+K+24*b+(4*a+2)+50)*(R+1)^2
  nlinarith only [hnR,hDR,hload,hsp,hl,hth,hp,hlog,hL,hf,hmul,hRs]

end Lax263307Proofs.NativeNodeResource
