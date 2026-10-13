import Lax263307.ConditionalRoutes
import Mathlib.Tactic

namespace Lax263307Proofs.ConditionalRoutes

open Lax263307.RouteDistributions Lax263307.ConditionalRoutes

/--
---
conclusion: Lax263307.ConditionalRoutes.conditional_correct
---
Use the uniform endpoint mass and multiply by n². Positive conditional
weights have the prescribed endpoints and inherit route validity.
-/
theorem conditional_correct {n q : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (u v : Fin n) :
    (∀ i, 0 ≤ conditional D u v i) ∧ (∑ i, conditional D u v i) = 1 ∧
      (∀ i, 0 < conditional D u v i → (D.route i).head? = some u ∧
        (D.route i).getLast? = some v ∧ (D.route i).Nodup ∧ (D.route i).IsChain G.Adj) := by
  classical
  have hpositive : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro i
    unfold conditional
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (D.nonnegative i)
    · rfl
  · have heq (i : Fin q) : conditional D u v i = (n : ℝ) ^ 2 *
        (if (D.route i).head? = some u ∧ (D.route i).getLast? = some v then D.probability i else 0) := by
      unfold conditional
      split_ifs <;> simp
    simp_rw [heq]
    rw [← Finset.mul_sum, D.uniform]
    exact mul_div_cancel₀ 1 (ne_of_gt hpositive)
  · intro i hi
    unfold conditional at hi
    split_ifs at hi with h
    · have hp : 0 < D.probability i := (mul_pos_iff_of_pos_left hpositive).mp hi
      have hv := D.valid i hp
      exact ⟨h.1, h.2, hv.1, hv.2.1⟩
    · exact (lt_irrefl _ hi).elim


/--
---
conclusion: Lax263307.ConditionalRoutes.mixture_identity
---
Every positive-probability route is nonempty and has a unique ordered
endpoint pair. All other terms in the endpoint sum vanish.
-/
theorem mixture_identity {n q : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (i : Fin q) :
    (∑ u, ∑ v, conditional D u v i) = (n : ℝ) ^ 2 * D.probability i := by
  classical
  by_cases hp : D.probability i = 0
  · simp [conditional, hp]
  · have hpositive : 0 < D.probability i := lt_of_le_of_ne (D.nonnegative i) (Ne.symm hp)
    have hne := (D.valid i hpositive).2.2
    let u := (D.route i).head hne
    let v := (D.route i).getLast hne
    have hs : (D.route i).head? = some u := List.head?_eq_some_head hne
    have ht : (D.route i).getLast? = some v := List.getLast?_eq_some_getLast hne
    simp only [conditional, hs, ht, Option.some.injEq, ite_and]
    simp


/--
---
conclusion: Lax263307.ConditionalRoutes.independent_pair_mixture
---
Factor the four finite endpoint sums into two separate sums and use
the mixture identity for each route. Cancel the factor n⁴.
-/
theorem independent_pair_mixture {n q : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (i j : Fin q) :
    (∑ u, ∑ v, ∑ s, ∑ t,
      conditional D u v i * conditional D s t j / (n : ℝ) ^ 4) =
        D.probability i * D.probability j := by
  classical
  simp_rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [mixture_identity]
  simp_rw [← Finset.sum_mul]
  rw [mixture_identity]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  field_simp

end Lax263307Proofs.ConditionalRoutes
