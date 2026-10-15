import Lax263307.EdgeBagBounds
import Lax263307.ForcedSeparation
import Lax263307.CutTraces
import Mathlib.Tactic

namespace Lax263307Proofs.LightSeparators

open scoped NNReal NNRat
open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators
open Lax263307.PowerBagBounds Lax263307.VertexSplitting
open Lax263307.RepeatedCutAccounting Lax263307.Entropy
open Lax455465.ProductNetwork Lax455465.ConcurrentFlow Lax455465.RationalEncoding

theorem logFactor_nonnegative (n : ℕ) : 0 ≤ logFactor n := by
  unfold logFactor
  apply div_nonneg _ (Real.log_pos (by norm_num)).le
  by_cases hn : n = 0
  · simp [hn]
  · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))

theorem logFactor_upper (n : ℕ) : logFactor n ≤ (Nat.log2 n : ℝ) + 1 := by
  by_cases hn : n = 0
  · simp [hn, logFactor]
  · have hp := (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
    rw [← Nat.log2_eq_log_two] at hp
    have hpr : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.log2 n + 1) := by exact_mod_cast hp
    have h := Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) hpr
    rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
    exact (div_le_iff₀ (Real.log_pos (by norm_num))).mpr h

theorem logFactor_mono {m n : ℕ} (positive : 0 < m) (bound : m ≤ n) : logFactor m ≤ logFactor n :=
  div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast positive) (by exact_mod_cast bound))
    (Real.log_pos (by norm_num)).le

theorem bounded_ratio (C : ℝ) (positive : 0 < C) :
    ∃ B : ℕ, 0 < B ∧ ∀ n r : ℕ, 0 < r → r ≤ n →
      C * logFactor (2 * r) ≤ (B : ℝ) * ((Nat.log2 (2 * n) : ℝ) + 1) := by
  let B := Nat.ceil C
  have hB : 0 < B := Nat.ceil_pos.mpr positive
  refine ⟨B, hB, ?_⟩
  intro n r hr hrn
  have hlog := (logFactor_mono (by omega : 0 < 2 * r) (Nat.mul_le_mul_left 2 hrn)).trans
    (logFactor_upper (2 * n))
  exact mul_le_mul (Nat.le_ceil C) hlog (logFactor_nonnegative _) (Nat.cast_nonneg B)


theorem sum_embedding {m n : ℕ} (f : Fin m ↪ Fin n) (x : Fin n → ℝ)
    (nonnegative : ∀ v, 0 ≤ x v) : (∑ v, x (f v)) ≤ ∑ v, x v := by
  classical
  calc
    _ = ∑ v ∈ Finset.univ.image f, x v := (Finset.sum_image (fun _ _ _ _ h => f.injective h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun v _ _ => nonnegative v)

theorem edge_cost_embedding {m n : ℕ} (H : SimpleGraph (Fin m)) (G : SimpleGraph (Fin n))
    [DecidableRel H.Adj] [DecidableRel G.Adj] (f : H ↪g G)
    (x : Fin n → ℝ) (nonnegative : ∀ v, 0 ≤ x v) :
    edgeCost H (x ∘ f) ≤ edgeCost G x := by
  classical
  unfold edgeCost adjacencyMass
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hnonneg (u v : Fin n) : 0 ≤ (if G.Adj u v then x u * x v else 0) := by
    split_ifs
    · exact mul_nonneg (nonnegative u) (nonnegative v)
    · exact le_refl _
  calc
    (∑ u : Fin m, ∑ v : Fin m, if H.Adj u v then (x ∘ f) u * (x ∘ f) v else 0) =
        ∑ u : Fin m, ∑ v : Fin m, if G.Adj (f u) (f v) then x (f u) * x (f v) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      simp only [Function.comp_apply, f.map_adj_iff]
    _ ≤ ∑ u : Fin m, ∑ v : Fin n, if G.Adj (f u) v then x (f u) * x v else 0 :=
      Finset.sum_le_sum (fun u _ => sum_embedding f.toEmbedding _ (hnonneg (f u)))
    _ ≤ _ := sum_embedding f.toEmbedding _ (fun u => Finset.sum_nonneg (fun v _ => hnonneg u v))


theorem small_piece {n : ℕ} (A B : Finset (Fin n)) (cover : A ∪ B = Finset.univ)
    (smaller : B.card ≤ A.card) : 2 * (B \ A).card ≤ n := by
  have h := Finset.card_union_add_card_inter A B
  rw [cover, Finset.card_univ, Fintype.card_fin] at h
  have hpart := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hpart
  omega


theorem remainder_scale (n r ℓ : ℕ) (hn : 0 < n) (hℓ : 0 < ℓ)
    (k : ℝ) (hk : 0 < k) (large : 2 * n < 3 * r) :
    0 < (ℓ : ℝ) * (n : ℝ) ^ 2 / (3 * k) ∧
      ((ℓ : ℝ) * (n : ℝ) ^ 2 / (3 * k)) * k ≤ (ℓ : ℝ) * (r : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hℓ' : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hr' : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hlarge : 2 * (n : ℝ) < 3 * (r : ℝ) := by exact_mod_cast large
  have hs : (n : ℝ) ^ 2 ≤ 3 * (r : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hlarge)) (show 0 ≤ 3 * (r : ℝ) + 2 * n by positivity)]
  refine ⟨by positivity, ?_⟩
  have heq : ((ℓ : ℝ) * (n : ℝ) ^ 2 / (3 * k)) * k = (ℓ : ℝ) * (n : ℝ) ^ 2 / 3 := by
    field_simp
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_left hs hℓ'.le]


end Lax263307Proofs.LightSeparators
