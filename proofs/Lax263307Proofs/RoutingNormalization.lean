import Lax263307.RoutingNormalization
import Mathlib.Tactic

namespace Lax263307Proofs.RoutingNormalization

open Lax263307.RoutingNormalization

theorem pair_mass {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (hn : 0 < n) (u v : Fin n)
    (positive : 0 < routed w E u v) :
    (∑ i, probability w E u v i) = 1 / (n : ℝ) ^ 2 := by
  classical
  have hterm (i : Fin q) : probability w E u v i =
      (if E u v i then w i else 0) / (routed w E u v * (n : ℝ) ^ 2) := by
    unfold probability
    split_ifs <;> simp
  simp_rw [hterm, ← Finset.sum_div]
  change routed w E u v / (routed w E u v * (n : ℝ) ^ 2) = _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

theorem total_mass {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (hn : 0 < n)
    (positive : ∀ u v, 0 < routed w E u v) :
    (∑ u, ∑ v, ∑ i, probability w E u v i) = 1 := by
  simp_rw [pair_mass w E hn _ _ (positive _ _)]
  simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

theorem pair_unique_sum {n q : ℕ} (E : Fin n → Fin n → Fin q → Prop)
    (unique : IsUniquePair E) (i : Fin q) (a : ℝ) (nonnegative : 0 ≤ a) :
    (by classical exact ∑ u, ∑ v, if E u v i then a else 0) ≤ a := by
  classical
  by_cases hexists : ∃ u v, E u v i
  · obtain ⟨u₀, v₀, hE⟩ := hexists
    have heq (u v : Fin n) : E u v i ↔ u = u₀ ∧ v = v₀ := by
      constructor
      · intro h
        exact unique i u v u₀ v₀ h hE
      · rintro ⟨rfl, rfl⟩
        exact hE
    simp_rw [heq, ite_and]
    simp
  · have hnone (u v : Fin n) : ¬E u v i := fun h => hexists ⟨u, v, h⟩
    simp_rw [if_neg (hnone _ _)]
    simpa using nonnegative

/--
---
conclusion: Lax263307.RoutingNormalization.normalization_correct
---
Sum within a commodity and divide by its positive routed mass and $n^2$.
The $n^2$ ordered pairs then contribute total mass one. Nonnegative flow
weights and positive denominators give nonnegative probabilities.
-/
theorem normalization_correct {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (hn : 0 < n)
    (nonnegative : ∀ i, 0 ≤ w i) (positive : ∀ u v, 0 < routed w E u v) :
    (∀ u v i, 0 ≤ probability w E u v i) ∧
      (∀ u v, (∑ i, probability w E u v i) = 1 / (n : ℝ) ^ 2) ∧
      (∑ u, ∑ v, ∑ i, probability w E u v i) = 1 := by
  classical
  refine ⟨?_, fun u v => pair_mass w E hn u v (positive u v), total_mass w E hn positive⟩
  intro u v i
  unfold probability
  split_ifs
  · exact div_nonneg (nonnegative i) (mul_nonneg (positive u v).le (sq_nonneg _))
  · exact le_refl 0

/--
---
conclusion: Lax263307.RoutingNormalization.normalized_load_bound
---
The lower bound on each routed mass bounds its inverse by gamma. Apply
this to each weighted cost, interchange the finite sums, and use endpoint
uniqueness to count each record at most once.
-/
theorem normalized_load_bound {n q : ℕ} (w : Fin q → ℝ)
    (E : Fin n → Fin n → Fin q → Prop) (hn : 0 < n)
    (nonnegative : ∀ i, 0 ≤ w i) (unique : IsUniquePair E)
    (γ : ℝ) (γ_positive : 0 < γ) (lower_bound : ∀ u v, 1 / γ ≤ routed w E u v)
    (cost : Fin q → ℝ) (cost_nonnegative : ∀ i, 0 ≤ cost i) :
    (∑ u, ∑ v, ∑ i, probability w E u v i * cost i) ≤
      γ / (n : ℝ) ^ 2 * (∑ i, w i * cost i) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hγ : 0 ≤ γ / (n : ℝ) ^ 2 := div_nonneg γ_positive.le hden.le
  have hpositive (u v : Fin n) : 0 < routed w E u v :=
    lt_of_lt_of_le (by positivity) (lower_bound u v)
  have hfactor (u v : Fin n) : 1 ≤ γ * routed w E u v := by
    have h := (div_le_iff₀ γ_positive).mp (lower_bound u v)
    nlinarith
  have hterm (u v : Fin n) (i : Fin q) : probability w E u v i * cost i ≤
      γ / (n : ℝ) ^ 2 * (if E u v i then w i * cost i else 0) := by
    by_cases hE : E u v i
    · simp only [probability, if_pos hE]
      have hw : w i / routed w E u v ≤ γ * w i := by
        apply (div_le_iff₀ (hpositive u v)).mpr
        have h := mul_le_mul_of_nonneg_left (hfactor u v) (nonnegative i)
        nlinarith
      have heq : w i / (routed w E u v * (n : ℝ) ^ 2) * cost i =
          (w i / routed w E u v * cost i) / (n : ℝ) ^ 2 := by ring
      rw [heq]
      have h := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hw (cost_nonnegative i)) hden.le
      calc
        (w i / routed w E u v * cost i) / (n : ℝ) ^ 2 ≤
            (γ * w i * cost i) / (n : ℝ) ^ 2 := h
        _ = γ / (n : ℝ) ^ 2 * (w i * cost i) := by ring
    · simp [probability, hE]
  have hswap : (∑ u, ∑ v, ∑ i, γ / (n : ℝ) ^ 2 * (if E u v i then w i * cost i else 0)) =
      ∑ i, γ / (n : ℝ) ^ 2 * ∑ u, ∑ v, if E u v i then w i * cost i else 0 := by
    conv_lhs => arg 2; ext u; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  calc
    (∑ u, ∑ v, ∑ i, probability w E u v i * cost i) ≤
        ∑ u, ∑ v, ∑ i, γ / (n : ℝ) ^ 2 * (if E u v i then w i * cost i else 0) :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun i _ => hterm u v i
    _ = ∑ i, γ / (n : ℝ) ^ 2 * ∑ u, ∑ v, if E u v i then w i * cost i else 0 := hswap
    _ ≤ ∑ i, γ / (n : ℝ) ^ 2 * (w i * cost i) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (pair_unique_sum E unique i _
        (mul_nonneg (nonnegative i) (cost_nonnegative i))) hγ
    _ = γ / (n : ℝ) ^ 2 * (∑ i, w i * cost i) := (Finset.mul_sum _ _ _).symm


end Lax263307Proofs.RoutingNormalization
