import Lax263307.LinearRelaxation
import Mathlib.Data.Rat.Defs

/-!
---
title: Descending target search in Solve
type: lemma
---
`Solve` tries targets in descending order. A failed target $k$ is accompanied
by a proof that every independent set has size less than $k$. A successful
target returns an independent set of size at least $\rho k$.
The first successful target is therefore a certified upper bound on the
independence number, and the returned set retains the factor $\rho$ of that
bound. The zero target provides the terminating empty-set case.

# Attribution

Bonnet–Chang, Algorithm 1 and the last paragraph of the proof of Lemma 14.
-/

namespace Lax263307.TargetSearch

/-- Try positive targets in decreasing order, falling back to the empty set. -/
def search {n : ℕ} (attempt : ℕ → Option (Finset (Fin n))) :
    ℕ → Finset (Fin n) × ℕ
  | 0 => (∅, 0)
  | k + 1 => match attempt (k + 1) with
    | some I => (I, k + 1)
    | none => search attempt k

/-- The target loop preserves the upper-bound and approximation invariants. -/
axiom search_correct {n : ℕ} (G : SimpleGraph (Fin n)) (ρ : ℝ)
    (attempt : ℕ → Option (Finset (Fin n)))
    (success : ∀ k, k ≤ n → ∀ I, attempt k = some I →
      G.IsIndepSet (I : Set (Fin n)) ∧ ρ * k ≤ I.card)
    (failure : ∀ k, 0 < k → k ≤ n → attempt k = none →
      ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card < k) :
    let result := search attempt n
    G.IsIndepSet (result.1 : Set (Fin n)) ∧
      (∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card ≤ result.2) ∧
      result.2 ≤ n ∧ ρ * result.2 ≤ result.1.card

end Lax263307.TargetSearch
