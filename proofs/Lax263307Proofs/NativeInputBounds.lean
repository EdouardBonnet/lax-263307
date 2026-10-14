import Lax263307.WeightedIndependentSet
import Lax455465Proofs.WordSize

namespace Lax263307Proofs.NativeInputBounds

open Lax263307 WeightedIndependentSet

def height {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : ℕ := rationalBitSize w ε+1

def magnitude {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : ℕ := 2^height w ε

theorem parameter_length {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) :
    (encodeParameters w ε).length=3*n+3 := by
  simp [encodeParameters,encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const,Nat.mul_comm]

theorem order_le_bits {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : n≤rationalBitSize w ε := by
  have h := Lax455465Proofs.WordSize.length_le (encodeParameters w ε)
  rw [parameter_length] at h
  change 3*n+3≤rationalBitSize w ε at h
  omega

theorem parameters_bound {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) :
    ∀ z∈encodeParameters w ε,z<magnitude w ε := by
  intro z hz
  exact (Lax455465Proofs.WordSize.member_bound _ _ hz).trans_le
    (Nat.pow_le_pow_right (by decide) (by dsimp [height,rationalBitSize]; omega))

theorem weight_bounds {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) :
    ∀ v,(w v).num.natAbs≤magnitude w ε ∧ (w v).den≤magnitude w ε := by
  intro v
  have hp : encodeRational (w v)⊆encodeParameters w ε := by
    intro z hz
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨w v,List.mem_ofFn.mpr ⟨v,rfl⟩,hz⟩
  exact ⟨(parameters_bound w ε _ (hp (by simp [encodeRational]))).le,
    (parameters_bound w ε _ (hp (by simp [encodeRational]))).le⟩

theorem accuracy_bounds {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) :
    ε.num.natAbs≤magnitude w ε ∧ ε.den≤magnitude w ε := by
  exact ⟨(parameters_bound w ε _ (List.mem_append_right _ (by simp [encodeRational]))).le,
    (parameters_bound w ε _ (List.mem_append_right _ (by simp [encodeRational]))).le⟩

theorem magnitude_positive {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : 1≤magnitude w ε :=
  Nat.one_le_pow _ _ (by decide)

theorem order_bound {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : n<magnitude w ε := by
  have h := order_le_bits w ε
  have hp : rationalBitSize w ε+1<2^(rationalBitSize w ε+1) := Nat.lt_two_pow_self
  dsimp [magnitude,height]
  omega

theorem input_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (ε : ℚ) : ∀ z∈encodeInput G w ε,z<magnitude w ε := by
  intro z hz
  simp only [encodeInput,List.mem_append,List.mem_singleton] at hz
  rcases hz with (rfl|hmatrix)|hparameters
  · exact order_bound w ε
  · simp only [List.mem_flatten,List.mem_ofFn] at hmatrix
    obtain ⟨row,⟨u,rfl⟩,hz⟩ := hmatrix
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hz
    have hp : 1<magnitude w ε := by
      dsimp [magnitude,height]
      have h := Nat.two_pow_pos (rationalBitSize w ε)
      rw [pow_succ]
      omega
    split_ifs <;> omega
  · exact parameters_bound w ε _ hparameters

end Lax263307Proofs.NativeInputBounds
