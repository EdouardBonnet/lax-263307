import Lax263307.SeparatorComponents
import Lax263307.ComponentCuts

/-!
---
title: Combining recursive answers in round-or-cut
type: theorem
---
Suppose conditioning gives costs of total mass $k$, and the deleted
separator has cost at most $\delta k$. Each remaining part returns an
independent set of size at least $(1-\delta)^h u_C$, where $u_C$ bounds
the part's independence number. Either some conditioned part cost exceeds
$u_C$, giving a valid violated cut, or the union of the returned sets is
independent and has size at least $(1-\delta)^{h+1}k$.

# Attribution

Bonnet–Chang, equation (24) and the round-or-cut step in Lemma 14.
-/

namespace Lax263307.RecursiveRounding

open LinearRelaxation SeparatorComponents

/-- Independent answers on different parts combine, and their sizes add. -/
axiom combine_independent {n : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (P : Partition G S ι)
    (I : ι → Finset (Fin n)) (inside : ∀ i, I i ⊆ P.vertices i)
    (independent : ∀ i, G.IsIndepSet (I i : Set (Fin n))) :
    G.IsIndepSet (combine I : Set (Fin n)) ∧ (combine I).card = ∑ i, (I i).card

/-- One query returns a sufficiently large set or a valid separating inequality. -/
axiom round_or_cut {n r : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (k h : ℕ) (δ : ℝ)
    (δ_nonnegative : 0 ≤ δ) (δ_small : δ ≤ 1)
    (y : MomentVector n r) (A S : Finset (Fin n)) (P : Partition G S ι)
    (size : A.card ≤ r) (positive : 0 < value y A)
    (mass : (∑ v, conditioned y A v) = k)
    (light : ∑ v ∈ S, conditioned y A v ≤ δ * k)
    (I : ι → Finset (Fin n)) (u : ι → ℕ)
    (inside : ∀ i, I i ⊆ P.vertices i)
    (independent : ∀ i, G.IsIndepSet (I i : Set (Fin n)))
    (bounds : ∀ i, IsIndependenceBound G (P.vertices i) (u i))
    (approximation : ∀ i, (1 - δ) ^ h * (u i : ℝ) ≤ (I i).card) :
    (G.IsIndepSet (combine I : Set (Fin n)) ∧
      (1 - δ) ^ (h + 1) * (k : ℝ) ≤ (combine I).card) ∨
    ∃ i, (∀ z ∈ independentSetHull G k r,
      ∑ v ∈ P.vertices i, value z (insert v A) ≤ (u i : ℝ) * value z A) ∧
      (u i : ℝ) * value y A < ∑ v ∈ P.vertices i, value y (insert v A)

end Lax263307.RecursiveRounding
