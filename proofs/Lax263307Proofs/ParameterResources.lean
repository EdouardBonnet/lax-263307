import Lax263307.ParameterResources
import Mathlib.Tactic

set_option maxHeartbeats 2000000

namespace Lax263307Proofs.ParameterResources

open Lax263307.AlgorithmParameters Lax263307.ParameterResources

theorem logarithm_mono (n : ℕ) : Nat.log2 n + 1 ≤ logarithm n := by
  unfold logarithm
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1

theorem order_bound (n : ℕ) (positive : 0 < n) : n + 1 ≤ 2 ^ logarithm n := by
  have h := Nat.lt_pow_succ_log_self Nat.one_lt_two (2 * n)
  rw [← Nat.log2_eq_log_two] at h
  exact (show n + 1 ≤ 2 * n by omega).trans h.le

theorem cutoff_eq_level (a K B n D : ℕ) : cutoff a K B n D = level a K B n D := by
  have h : targetThreshold a K B n D ≤ level a K B n D := by
    unfold level sparsity
    have hfactor : 1 ≤ Nat.log2 n + 1 := by omega
    nlinarith
  exact max_eq_right h

theorem level_bound (a K B n D : ℕ) (positive : 0 < D) :
    level a K B n D ≤
      (2 * K * (12 * B + 1) ^ (4 * a + 2)) * (D * logarithm n) ^ (4 * a + 3) := by
  let X := D * logarithm n
  have hlog : 0 < logarithm n := by unfold logarithm; omega
  have hX : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr (by dsimp [X]; positivity)
  have hDX : logarithm n ≤ X := Nat.le_mul_of_pos_left _ positive
  have hLX : Nat.log2 n + 1 ≤ X := (logarithm_mono n).trans hDX
  have hload : load B n D + 1 ≤ (12 * B + 1) * X := by
    dsimp [load, X]
    nlinarith
  have hpow := Nat.pow_le_pow_left hload (4 * a + 2)
  have hp : sparsity a K B n D ≤ 2 * K * ((12 * B + 1) * X) ^ (4 * a + 2) := by
    unfold sparsity targetThreshold
    simpa only [mul_assoc] using Nat.mul_le_mul_left (2 * K) hpow
  have hlevel := Nat.mul_le_mul hp hLX
  change level a K B n D ≤ _ at hlevel
  change level a K B n D ≤ (2 * K * (12 * B + 1) ^ (4 * a + 2)) * X ^ (4 * a + 3)
  calc
    _ ≤ 2 * K * ((12 * B + 1) * X) ^ (4 * a + 2) * X := hlevel
    _ = _ := by
      rw [mul_pow, show 4 * a + 3 = (4 * a + 2) + 1 by omega, pow_succ]
      ring

theorem denominator_eq (a K B n D : ℕ) :
    floorDenominator a K B n D = 2 * n * level a K B n D := by
  unfold floorDenominator level
  ring

theorem dimensions_envelope (n r L : ℕ) (order : n + 1 ≤ 2 ^ L) :
    Lax263307.MomentLP.dimension n r ≤ 2 ^ (r + 3 + L * (r + 2)) := by
  have hN := Lax263307.CoordinateCatalog.catalog_bound n r
  change Lax263307.MomentLP.dimension n r ≤ _ at hN
  have hpow := Nat.pow_le_pow_left order (r + 2)
  have hr : r + 3 ≤ 2 ^ (r + 3) := Nat.lt_two_pow_self.le
  calc
    _ ≤ (r + 3) * (n + 1) ^ (r + 2) := hN
    _ ≤ 2 ^ (r + 3) * (2 ^ L) ^ (r + 2) := Nat.mul_le_mul hr hpow
    _ = _ := by rw [← pow_mul, ← pow_add]

/--
---
conclusion: Lax263307.ParameterResources.resource_bound
---
-/
theorem resource_bound (a K B : ℕ) (hK : 0 < K) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧ ∀ n D : ℕ, 0 < n → 0 < D →
      resource a K B n D ≤ 2 ^ (C * (D * logarithm n) ^ d) := by
  let c := 2 * K * (12 * B + 1) ^ (4 * a + 2)
  let d := 4 * a + 3
  let A := c * (c + 2) + 2 * (c + 3) + 20
  let e := 2 * d + 2
  refine ⟨3 * A + 6, e, by positivity, by dsimp [e]; omega, ?_⟩
  intro n D hn hD
  let L := logarithm n
  let X := D * L
  let r := level a K B n D
  let N := Lax263307.MomentLP.dimension n r
  let Q := floorDenominator a K B n D
  let M := radiusDenominator a K B n D
  let U := 2 ^ (A * X ^ e)
  have hLpos : 0 < L := by dsimp [L, logarithm]; omega
  have hXpos : 0 < X := by dsimp [X]; positivity
  have hX1 : 1 ≤ X := hXpos
  have hL : L ≤ X := Nat.le_mul_of_pos_left _ hD
  have hDX : D ≤ X := Nat.le_mul_of_pos_right _ hLpos
  have hd : 0 < d := by dsimp [d]; omega
  have hXd : X ≤ X ^ d := le_self_pow hX1 (by omega)
  have hXdp : 1 ≤ X ^ d := Nat.one_le_pow _ _ hX1
  have hr : r ≤ c * X ^ d := level_bound a K B n D hD
  have hrpos : 0 < r := by dsimp [r, level, sparsity, targetThreshold]; positivity
  have hQpos : 0 < Q := by
    rw [show Q = 2 * n * r from denominator_eq a K B n D]
    positivity
  have hNpos : 0 < N := Lax263307.CoordinateCatalog.catalog_positive n r
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hU1 : 1 ≤ U := hUpos
  have hnexp : n + 1 ≤ 2 ^ L := order_bound n hn
  have hrExp : r ≤ 2 ^ (c * X ^ d) := hr.trans Nat.lt_two_pow_self.le
  have hQ : Q ≤ 2 ^ ((c + 2) * X ^ d) := by
    calc
      Q = 2 * n * r := denominator_eq a K B n D
      _ ≤ 2 * 2 ^ L * 2 ^ (c * X ^ d) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega : n ≤ 2 ^ L)) hrExp
      _ = 2 ^ (1 + L + c * X ^ d) := by
        conv_rhs => rw [pow_add, pow_add]
        norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith [hL.trans hXd])
  have hQr : Q ^ r ≤ 2 ^ (c * (c + 2) * X ^ (2 * d)) := by
    calc
      _ ≤ (2 ^ ((c + 2) * X ^ d)) ^ r := Nat.pow_le_pow_left hQ r
      _ = 2 ^ (((c + 2) * X ^ d) * r) := (pow_mul 2 ((c + 2) * X ^ d) r).symm
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        calc
          _ ≤ ((c + 2) * X ^ d) * (c * X ^ d) := Nat.mul_le_mul_left _ hr
          _ = _ := by rw [show 2 * d = d + d by omega, pow_add]; ring
  have hr3 : r + 3 ≤ (c + 3) * X ^ d := by nlinarith
  have hN : N ≤ 2 ^ (2 * (c + 3) * X ^ (d + 1)) := by
    have hN' := dimensions_envelope n r L hnexp
    apply hN'.trans
    apply Nat.pow_le_pow_right (by decide)
    have hprod := Nat.mul_le_mul hL (show r + 2 ≤ (c + 3) * X ^ d by omega)
    calc
      _ ≤ (c + 3) * X ^ d + X * ((c + 3) * X ^ d) := by omega
      _ = ((c + 3) * X ^ d) * (1 + X) := by ring
      _ ≤ ((c + 3) * X ^ d) * (2 * X) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hn2 : n ^ 2 ≤ 2 ^ (2 * L) := by
    have h := Nat.pow_le_pow_left (show n ≤ 2 ^ L by omega) 2
    simpa only [← pow_mul, Nat.mul_comm L 2] using h
  have hD2 : D ^ 2 ≤ 2 ^ (2 * D) := by
    have h := Nat.pow_le_pow_left (Nat.lt_two_pow_self.le : D ≤ 2 ^ D) 2
    simpa only [← pow_mul, Nat.mul_comm D 2] using h
  have hM : M ≤ U := by
    have hpoly : 8 + 2 * (c + 3) * X ^ (d + 1) + 2 * L + 2 * D +
        c * (c + 2) * X ^ (2 * d) ≤ A * X ^ e := by
      have h1e : 1 ≤ X ^ e := Nat.one_le_pow _ _ hX1
      have hXe : X ≤ X ^ e := le_self_pow hX1 (by dsimp [e]; omega)
      have hp1 := Nat.pow_le_pow_right hX1 (show d + 1 ≤ e by dsimp [e]; omega)
      have hp2 := Nat.pow_le_pow_right hX1 (show 2 * d ≤ e by dsimp [e]; omega)
      have hco1 := Nat.mul_le_mul_left (2 * (c + 3)) hp1
      have hco2 := Nat.mul_le_mul_left (c * (c + 2)) hp2
      have hLe := hL.trans hXe
      have hDe := hDX.trans hXe
      dsimp only [A]
      nlinarith
    calc
      M = 256 * N * n ^ 2 * D ^ 2 * Q ^ r := rfl
      _ ≤ 256 * 2 ^ (2 * (c + 3) * X ^ (d + 1)) * 2 ^ (2 * L) * 2 ^ (2 * D) *
          2 ^ (c * (c + 2) * X ^ (2 * d)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 256 hN) hn2) hD2) hQr
      _ = 2 ^ (8 + 2 * (c + 3) * X ^ (d + 1) + 2 * L + 2 * D + c * (c + 2) * X ^ (2 * d)) := by
        rw [show (256 : ℕ) = 2 ^ 8 by decide]
        repeat rw [← pow_add]
      _ ≤ U := Nat.pow_le_pow_right (by decide) hpoly
  have hQpow : Q ≤ Q ^ r := le_self_pow (by omega) (by omega)
  have hPowM : Q ^ r ≤ M :=
    Nat.le_mul_of_pos_left _ (by dsimp [N]; positivity : 0 < 256 * N * n ^ 2 * D ^ 2)
  have hnM : n ≤ M := (show n ≤ Q by rw [show Q = 2 * n * r from denominator_eq a K B n D]; nlinarith).trans
    (hQpow.trans hPowM)
  have hrM : r ≤ M := (show r ≤ Q by rw [show Q = 2 * n * r from denominator_eq a K B n D]; nlinarith).trans
    (hQpow.trans hPowM)
  have hNM : N ≤ M := by
    have hrest : 0 < 256 * n ^ 2 * D ^ 2 * Q ^ r := by positivity
    have h := Nat.le_mul_of_pos_right N hrest
    convert h using 1; first | rfl | (dsimp [M, radiusDenominator, N, Q, r]; ring)
  have hDM : D ≤ M := by
    have hrest : 0 < 256 * N * n ^ 2 * Q ^ r := by positivity
    have hDsq : D ≤ D ^ 2 := by simpa only [pow_two] using Nat.le_mul_self D
    have h := hDsq.trans (Nat.le_mul_of_pos_right (D ^ 2) hrest)
    convert h using 1 <;> first | rfl | (dsimp [M, radiusDenominator, N, Q, r]; ring)
  have hpR : sparsity a K B n D ≤ r := Nat.le_mul_of_pos_right _ (by omega)
  have hloadR : load B n D ≤ r := by
    have hpow : load B n D + 1 ≤ (load B n D + 1) ^ (4 * a + 2) :=
      le_self_pow (by omega) (by omega)
    have hcoeff : (load B n D + 1) ^ (4 * a + 2) ≤ sparsity a K B n D := by
      unfold sparsity targetThreshold
      simpa only [mul_assoc] using Nat.le_mul_of_pos_left ((load B n D + 1) ^ (4 * a + 2))
        (by positivity : 0 < 2 * K)
    exact (show load B n D ≤ load B n D + 1 by omega).trans (hpow.trans (hcoeff.trans hpR))
  have hprec : precision a K B n D ≤ 3 * U := by change M + 2 ≤ _; omega
  have hiter : iterations a K B n D ≤ 32 * U ^ 3 := by
    have hnu : N ≤ U := hNM.trans hM
    have hp := Nat.mul_le_mul hprec hnu
    have hleft : N + 1 ≤ 2 * U := by omega
    have hright : precision a K B n D * N + 1 ≤ 4 * U ^ 2 := by
      have hUsq : 1 ≤ U ^ 2 := Nat.one_le_pow 2 U hUpos
      nlinarith
    have h := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hleft) hright
    change iterations a K B n D ≤ _ at h
    convert h using 1; ring
  have hbrute : (n + 1) ^ cutoff a K B n D ≤ U := by
    rw [cutoff_eq_level]
    have h := Nat.pow_le_pow_left hnexp r
    rw [← pow_mul] at h
    apply h.trans
    apply Nat.pow_le_pow_right (by decide)
    have hp := Nat.mul_le_mul hL hr
    have he : X * (c * X ^ d) = c * X ^ (d + 1) := by rw [pow_succ]; ring
    rw [he] at hp
    have hde := Nat.pow_le_pow_right hX1 (show d + 1 ≤ e by dsimp [e]; omega)
    have hcA : c ≤ A := by dsimp [A]; nlinarith
    exact hp.trans (Nat.mul_le_mul hcA hde)
  have hsmall : resource a K B n D ≤ 64 * U ^ 3 := by
    have hnU := hnM.trans hM
    have hDU := hDM.trans hM
    have hloadU := hloadR.trans (hrM.trans hM)
    have hpU := hpR.trans (hrM.trans hM)
    have hrU := hrM.trans hM
    have hNU := hNM.trans hM
    have hU3 : U ≤ U ^ 3 := le_self_pow hU1 (by decide)
    dsimp only [resource]
    change n + D + load B n D + sparsity a K B n D + r + N + M +
      precision a K B n D + iterations a K B n D + (n + 1) ^ cutoff a K B n D ≤ _
    nlinarith
  calc
    resource a K B n D ≤ 64 * U ^ 3 := hsmall
    _ = 2 ^ (6 + 3 * A * X ^ e) := by
      dsimp [U]
      rw [show (64 : ℕ) = 2 ^ 6 by decide, ← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ 2 ^ ((3 * A + 6) * X ^ e) := by
      apply Nat.pow_le_pow_right (by decide)
      have hXe1 : 1 ≤ X ^ e := Nat.one_le_pow _ _ hX1
      nlinarith

end Lax263307Proofs.ParameterResources
