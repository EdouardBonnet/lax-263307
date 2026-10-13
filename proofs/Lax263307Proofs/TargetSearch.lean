import Lax263307.TargetSearch
import Mathlib.Tactic

namespace Lax263307Proofs.TargetSearch

open Lax263307.TargetSearch

theorem search_invariants {n : ℕ} (G : SimpleGraph (Fin n)) (ρ : ℝ)
    (attempt : ℕ → Option (Finset (Fin n))) (N : ℕ)
    (success : ∀ k, k ≤ N → ∀ I, attempt k = some I →
      G.IsIndepSet (I : Set (Fin n)) ∧ ρ * k ≤ I.card)
    (failure : ∀ k, 0 < k → k ≤ N → attempt k = none →
      ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card < k)
    (k : ℕ) (hk : k ≤ N)
    (upper : ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card ≤ k) :
    let result := search attempt k
    G.IsIndepSet (result.1 : Set (Fin n)) ∧
      (∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card ≤ result.2) ∧
      result.2 ≤ k ∧ ρ * result.2 ≤ result.1.card := by
  induction k with
  | zero =>
    simp only [search, mul_zero, Finset.card_empty, Nat.cast_zero, le_refl, and_true]
    exact ⟨by intro a ha; simp at ha, upper⟩
  | succ k ih =>
    cases he : attempt (k + 1) with
    | some I =>
      obtain ⟨hI, hsize⟩ := success _ hk I he
      simp only [search, he]
      exact ⟨hI, upper, le_rfl, hsize⟩
    | none =>
      have upper' : ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card ≤ k := by
        intro J hJ
        exact Nat.le_of_lt_succ (failure _ (by omega) hk he J hJ)
      obtain ⟨hI, hu, hk', hsize⟩ := ih (by omega) upper'
      simp only [search, he]
      exact ⟨hI, hu, hk'.trans (Nat.le_succ k), hsize⟩

/--
---
conclusion: Lax263307.TargetSearch.search_correct
---
Induct over the decreasing target. A rejection at `k+1` bounds all independent
sets by `k`, preserving the induction invariant. A success uses that invariant
as the certified upper bound. Initially every independent set has at most
the graph's order, and the zero case returns the empty set.

# Attribution

Bonnet–Chang, Algorithm 1 and Lemma 14.
-/
theorem search_correct {n : ℕ} (G : SimpleGraph (Fin n)) (ρ : ℝ)
    (attempt : ℕ → Option (Finset (Fin n)))
    (success : ∀ k, k ≤ n → ∀ I, attempt k = some I →
      G.IsIndepSet (I : Set (Fin n)) ∧ ρ * k ≤ I.card)
    (failure : ∀ k, 0 < k → k ≤ n → attempt k = none →
      ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card < k) :
    let result := search attempt n
    G.IsIndepSet (result.1 : Set (Fin n)) ∧
      (∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card ≤ result.2) ∧
      result.2 ≤ n ∧ ρ * result.2 ≤ result.1.card := by
  apply search_invariants G ρ attempt n success failure n le_rfl
  intro J _
  simpa using Finset.card_le_univ J

end Lax263307Proofs.TargetSearch
