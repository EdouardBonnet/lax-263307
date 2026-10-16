import Lax263307Proofs.NativeRootResource
import Lax263307Proofs.RoundingBounds
import Lax263307.RecursiveAlgorithm
import Lax263307Proofs.QPTASRuntime

namespace Lax263307Proofs.NativeFinalBounds

open Lax263307 AlgorithmParameters RecursiveAlgorithm

def inputLog (n : ℕ) : ℕ := Nat.log2 (n+2)+1

theorem half_accuracy (ε : ℚ) (hε : 0<ε) : ⌈(ε/2)⁻¹⌉₊≤2*⌈ε⁻¹⌉₊ := by
  apply Nat.ceil_le.mpr
  have hc := Nat.le_ceil ε⁻¹
  have he : (ε/2)⁻¹=2*ε⁻¹ := by field_simp
  rw [he]
  push_cast
  linarith

theorem copy_order {n : ℕ} (weights : Fin n → ℚ) (ε : ℚ)
    (hw : ∀ v,0≤weights v) (hn : 0<n) (hε : 0<ε)
    (hmax : 0<WeightRounding.maximumWeight weights) :
    ∑ v,WeightRounding.copies weights ε v≤2*n^2*⌈ε⁻¹⌉₊ := by
  have h := Lax263307.RoundingBounds.total_copy_bound weights ε hw hn hε hmax
  have hc := Nat.le_ceil ε⁻¹
  have he : (2*(n : ℚ)^2)/ε=2*(n : ℚ)^2*ε⁻¹ := by ring
  rw [he] at h
  have hc' := mul_le_mul_of_nonneg_left hc (show (0 : ℚ)≤2*(n : ℚ)^2 by positivity)
  have ht := h.trans hc'
  exact_mod_cast ht

/-- The blow-up's logarithm is bounded in the original input parameters. -/
theorem blowup_log (n N E : ℕ) (hE : 0<E) (hN : N≤2*n^2*E) : logarithm N≤6*(E*inputLog n) := by
  let L := inputLog n
  have hL : 1≤L := by dsimp [L,inputLog]; omega
  have hn : n≤2^L := by
    have hh : n+2<2^L := Nat.lt_pow_of_log_lt (by decide) (by
      change Nat.log 2 (n+2)<Nat.log2 (n+2)+1
      rw [Nat.log2_eq_log_two]; omega)
    omega
  have he : E≤2^E := Nat.lt_two_pow_self.le
  have hp : 2*N≤2^(2+2*L+E) := by
    calc
      2*N≤4*(n^2*E) := by nlinarith only [hN]
      _≤4*((2^L)^2*2^E) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hn 2) he)
      _=_ := by rw [←pow_mul,←pow_add]; norm_num; congr 1; ring
  have ht : 2*N<2^(3+2*L+E) := by
    have hx : 0<2^(2+2*L+E) := Nat.two_pow_pos _
    have heq : 3+2*L+E=(2+2*L+E)+1 := by omega
    rw [heq,pow_succ]
    omega
  have hl : Nat.log 2 (2*N)<3+2*L+E := Nat.log_lt_of_lt_pow' (by omega : 3+2*L+E≠0) ht
  have hlog : logarithm N≤3+2*L+E := by
    unfold logarithm
    rw [Nat.log2_eq_log_two]
    omega
  have heL : E≤E*L := Nat.le_mul_of_pos_right _ hL
  have hLe : L≤E*L := Nat.le_mul_of_pos_left _ hE
  have hpos : 1≤E*L := Nat.mul_pos hE (by omega)
  exact hlog.trans (by nlinarith only [heL,hLe,hpos])

theorem denominator_bound (N : ℕ) (ε : ℚ) (hε : 0<ε) :
    accuracyDenominator N (ε/2)≤24*⌈ε⁻¹⌉₊*logarithm N := by
  have hc := half_accuracy ε hε
  have hd := RecursionDepth.logarithmic_bound N
  have hl := ParameterResources.logarithm_mono N
  have hp : 1≤logarithm N := by unfold logarithm; omega
  have hdepth : RecursionDepth.depth N+1≤3*logarithm N := by omega
  unfold accuracyDenominator
  have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hdepth) hc
  convert hh using 1 <;> ring

/-- The final weighted envelope has exactly the main theorem's dependence
on inverse accuracy and log of the original graph order. -/
theorem weighted_envelope (C d n N : ℕ) (ε : ℚ) (hε : 0<ε)
    (hN : N≤2*n^2*⌈ε⁻¹⌉₊) :
    NativeRootResource.envelope C d N (accuracyDenominator N (ε/2))≤
      2^((C*864^d)*(⌈ε⁻¹⌉₊*inputLog n)^(3*d)) := by
  let E := ⌈ε⁻¹⌉₊
  let L := inputLog n
  let X := E*L
  have hE : 0<E := Nat.ceil_pos.mpr (inv_pos.mpr hε)
  have hL : 1≤L := by dsimp [L,inputLog]; omega
  have hl := blowup_log n N E hE hN
  have hd := denominator_bound N ε hε
  have hbase : accuracyDenominator N (ε/2)*logarithm N≤864*X^3 := by
    have h1 := Nat.mul_le_mul_right (logarithm N) hd
    have h2 := Nat.pow_le_pow_left hl 2
    have h3 : E^3*L^2≤X^3 := by
      dsimp [X]
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL (by omega))
    calc
      _≤24*E*(logarithm N)^2 := by nlinarith only [h1]
      _≤24*E*(6*(E*L))^2 := Nat.mul_le_mul_left _ h2
      _=864*(E^3*L^2) := by ring
      _≤864*X^3 := Nat.mul_le_mul_left _ h3
  apply Nat.pow_le_pow_right (by decide)
  have hh := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase d)
  convert hh using 1 <;> rw [mul_pow] <;> simp only [pow_mul] <;> ring

theorem final_time (C d q e n N ℓ : ℕ) (ε : ℚ) (hε : 0<ε)
    (hN : N≤2*n^2*⌈ε⁻¹⌉₊) :
    NativeRootResource.envelope C d N (accuracyDenominator N (ε/2))+q*(ℓ+1)^e≤
      QPTASRuntime.timeBound (C*864^d+q+1) (max (3*d) e) n ℓ ε := by
  have h := weighted_envelope C d n N ε hε hN
  have hE : 0<⌈ε⁻¹⌉₊ := Nat.ceil_pos.mpr (inv_pos.mpr hε)
  have hX : 1≤⌈ε⁻¹⌉₊*inputLog n := Nat.mul_pos hE (by dsimp [inputLog]; omega)
  apply Nat.add_le_add
  · apply h.trans
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hX (le_max_left _ _))
  · exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (le_max_right _ _))

/-- A maximum-weight vertex alone receives at least n copies. This places
original-order frontend/output work inside the positive blow-up's envelope. -/
theorem original_order_le_copy_order {n : ℕ} (w : Fin n → ℚ) (ε : ℚ)
    (hn : 0<n) (hε : 0<ε) (hε1 : ε≤1) (hW : 0<WeightRounding.maximumWeight w) :
    n≤∑ v,WeightRounding.copies w ε v := by
  classical
  have hmem : WeightRounding.maximumWeight w∈insert 0 (Finset.univ.image w) :=
    Finset.max'_mem _ _
  obtain ⟨v,hv⟩ : ∃ v,w v=WeightRounding.maximumWeight w := by
    rcases Finset.mem_insert.mp hmem with hz|himage
    · exact False.elim (by linarith)
    · obtain ⟨v,_,he⟩ := Finset.mem_image.mp himage
      exact ⟨v,he⟩
  have hquot : w v/WeightRounding.scale w ε=2*(n : ℚ)/ε := by
    rw [hv]
    unfold WeightRounding.scale
    have hnQ : (n : ℚ)≠0 := by exact_mod_cast hn.ne'
    field_simp [hW.ne',hε.ne',hnQ]
  have hc : n≤WeightRounding.copies w ε v := by
    dsimp [WeightRounding.copies,WeightRounding.roundedCopies]
    apply Nat.le_floor
    rw [hquot]
    apply (le_div_iff₀ hε).mpr
    have hmul := mul_le_mul_of_nonneg_left hε1 (show (0 : ℚ)≤n by positivity)
    nlinarith
  exact hc.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v))

end Lax263307Proofs.NativeFinalBounds
