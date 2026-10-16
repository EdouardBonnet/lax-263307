import Lax263307.MaxWeightIndependentSet
import Lax263307Proofs.NativeBlowUp

namespace Lax263307Proofs.MaxWeightIndependentSet

open Lax263307 Lax263307.MaxWeightIndependentSet WeightedIndependentSet
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

@[simp] theorem vertexCount_encode {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) :
    vertexCount (encodeInstance G w) = n := rfl

theorem input_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (ε : ℚ) :
    encodeInput G w ε = encodeInstance G w ++ encodeRational ε := by
  classical
  simp only [encodeInput, encodeInstance, encodeParameters, List.append_assoc]
  congr!

theorem matrix_entry {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (u v : Fin n) :
    (encodeInstance G w).getD (1 + u.val*n + v.val) 0 = if G.Adj u v then 1 else 0 := by
  classical
  have h := NativeBlowUp.matrix_coordinate (fun u v : Fin n => if G.Adj u v then 1 else 0) u v
  have hi : u.val*n+v.val < n*n := by nlinarith [u.isLt, v.isLt]
  have hl := NativeBlowUp.matrix_length (fun u v : Fin n => if G.Adj u v then 1 else 0)
  simp only [encodeInstance, List.cons_append, List.nil_append,
    List.getD_eq_getElem?_getD]
  rw [show 1+u.val*n+v.val = (u.val*n+v.val)+1 by omega]
  rw [List.getElem?_cons_succ, List.getElem?_append_left (by change u.val*n+v.val < (NativeBlowUp.matrix _).length; rwa [hl])]
  change ((NativeBlowUp.matrix _)[u.val*n+v.val]?).getD 0 = _
  rw [h]
  rfl

@[simp] theorem decodeGraph_encode {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) :
    decodeGraph (encodeInstance G w) = G := by
  classical
  ext u v
  change Fin n at u v
  change (u ≠ v ∧ (encodeInstance G w).getD (1+u.val*n+v.val) 0 ≠ 0 ∧
    (encodeInstance G w).getD (1+v.val*n+u.val) 0 ≠ 0) ↔ G.Adj u v
  rw [matrix_entry, matrix_entry]
  constructor
  · rintro ⟨_, h, _⟩
    by_contra hn
    simp [hn] at h
  · intro h
    exact ⟨h.ne, by simp [h], by simp [h.symm]⟩

theorem weight_entry {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (v : Fin n) (j : ℕ) (hj : j < 3) :
    (encodeInstance G w)[1+n*n+3*v.val+j]? = (encodeRational (w v))[j]? := by
  classical
  let front := [n] ++ NativeWeightReduction.adjacency G
  have hf : front.length = 1+n*n := by
    simp [front, NativeWeightReduction.adjacency_length, Nat.add_comm]
  have h := NativeFrontend.prefixed_coordinate front [] (List.ofFn w) v.val j
    (by simpa using v.isLt) hj
  rw [hf] at h
  simpa only [front, List.append_nil, List.getElem_ofFn, encodeInstance,
    NativeWeightReduction.adjacency] using h

@[simp] theorem decodeWeights_encode {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) :
    decodeWeights (encodeInstance G w) = w := by
  classical
  funext v
  change Fin n at v
  have h0 := weight_entry G w v 0 (by decide)
  have h1 := weight_entry G w v 1 (by decide)
  have h2 := weight_entry G w v 2 (by decide)
  simp only [Nat.add_zero, encodeRational, List.getElem?_cons_zero,
    List.getElem?_cons_succ] at h0 h1 h2
  simp only [decodeWeights, vertexCount_encode, List.getD_eq_getElem?_getD, h0, h1, h2,
    Option.getD_some]
  by_cases h : (w v).num < 0
  · simp only [if_pos h, one_ne_zero, if_false]
    have hn : ((w v).num.natAbs : ℚ) = -((w v).num : ℚ) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (fun z : ℤ => (z:ℚ)) (Int.ofNat_natAbs_of_nonpos (le_of_lt h))
    rw [hn, neg_neg, Rat.num_div_den]
  · simp only [if_neg h, if_true]
    have hn : ((w v).num.natAbs : ℚ) = ((w v).num : ℚ) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun z : ℤ => (z:ℚ)) (Int.natAbs_of_nonneg (le_of_not_gt h))
    rw [hn, Rat.num_div_den]

@[simp] theorem decodeSolution_encode {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (I : Finset (Fin n)) : decodeSolution (encodeInstance G w) (encodeOutput I) = I := by
  ext v
  change Fin n at v
  simp [decodeSolution, encodeOutput, List.getD_eq_getElem, v.isLt]

theorem IsFeasible_encode {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (I : Finset (Fin n)) (hI : G.IsIndepSet (I : Set (Fin n))) :
    IsFeasible (encodeInstance G w) (encodeOutput I) := by
  refine ⟨by simp [encodeOutput], ?_, ?_⟩
  · intro b hb
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hb
    split_ifs <;> simp
  · rw [decodeGraph_encode, decodeSolution_encode]
    change G.IsIndepSet (I : Set (Fin n))
    exact hI

theorem objectiveValue_encode {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (I : Finset (Fin n)) :
    objectiveValue (encodeInstance G w) (encodeOutput I) = Real.toNNReal (weight w I) := by
  simp [objectiveValue]

theorem nonnegative {n : ℕ} {G : SimpleGraph (Fin n)} {w : Fin n → ℚ}
    {ε : ℚ} {I : Finset (Fin n)} (h : IsApproximation G w ε I) : 0 ≤ weight w I := by
  simpa [weight] using h.2 ∅ (by simp)

/-- Integer precision in lax-213208 corresponds to accuracy `1/(k+1)` here. -/
theorem approximation {n k : ℕ} (hk : 0 < k) {G : SimpleGraph (Fin n)}
    {w : Fin n → ℚ} {I : Finset (Fin n)}
    (h : IsApproximation G w (1/(k+1)) I) :
    Lax213208.Approximation.IsApproximation MaxWeightIndependentSet (1+1/(k:ℝ))
      (encodeInstance G w) (encodeOutput I) := by
  have hkR : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hI : (0:ℝ) ≤ weight w I := by exact_mod_cast nonnegative h
  refine ⟨le_add_of_nonneg_right (by positivity),
    IsFeasible_encode G w I h.1, ?_⟩
  intro z hz
  let J : Finset (Fin n) := decodeSolution (encodeInstance G w) z
  have hz' : G.IsIndepSet (J : Set (Fin n)) := by
    have hh := hz.2.2
    rw [decodeGraph_encode] at hh
    exact hh
  have hc := h.2 J hz'
  have hcR : (1-1/((k:ℝ)+1)) * (weight w J : ℝ)
      ≤ (weight w I : ℝ) := by
    have ht := (Rat.cast_le (K := ℝ)).mpr hc
    push_cast at ht
    exact ht
  have he : (1+1/(k:ℝ))*(1-1/((k:ℝ)+1)) = 1 := by
    field_simp
    ring
  have hr : 0 ≤ 1+1/(k:ℝ) := by positivity
  have hc' := mul_le_mul_of_nonneg_left hcR hr
  rw [← mul_assoc, he, one_mul] at hc'
  change (objectiveValue (encodeInstance G w) z : ℝ) ≤
    (1+1/(k:ℝ)) * (objectiveValue (encodeInstance G w) (encodeOutput I) : ℝ)
  rw [objectiveValue_encode, Real.coe_toNNReal _ hI]
  simp only [objectiveValue, decodeWeights_encode, Real.coe_toNNReal']
  exact max_le hc' (mul_nonneg hr hI)

end Lax263307Proofs.MaxWeightIndependentSet
