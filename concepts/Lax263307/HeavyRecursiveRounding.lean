import Lax263307.StrongComponentGaps
import Lax263307.ConditionedCosts
import Lax263307.RecursiveRounding

/-!
---
title: Recursive rounding after discarding light parts
type: lemma
---
Among at most $2n$ parts, those with conditioned cost at most
$\delta k/(4n)$ have total cost at most $\delta k/2$. Independent answers
at rounded targets on all heavier parts combine into an independent set,
losing a factor of at most $1-4\delta$ per recursive level.

# Formalization notes

The size guarantee is required only on heavy parts. The returned set from
every part must be independent and contained in that part. The estimates
apply with nonnegative accuracy parameter at most $1/4$.
-/

namespace Lax263307.HeavyRecursiveRounding

open LinearRelaxation SeparatorComponents
open ComponentCutEncoding

axiom ignored_cost {n : ℕ} {ι : Type} [Fintype ι] (c : ι → ℝ) (δ k : ℝ)
    (hn : 0 < n) (hδ : 0 ≤ δ) (hk : 0 ≤ k) (count : Fintype.card ι ≤ 2 * n) :
    (∑ i, if δ * k / (4 * n) < c i then 0 else c i) ≤ δ * k / 2

axiom heavy_union_size {n : ℕ} {ι : Type} [Fintype ι]
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (P : Partition G S ι)
    (x : Fin n → ℝ) (k : ℕ) (h : ℕ) (δ : ℝ)
    (hn : 0 < n) (hδ : 0 ≤ δ) (small : δ ≤ 1 / 4)
    (count : Fintype.card ι ≤ 2 * n)
    (mass : (∑ v, x v) = k) (light : ∑ v ∈ S, x v ≤ δ * k)
    (I : ι → Finset (Fin n)) (targets : ι → ℕ)
    (inside : ∀ i, I i ⊆ P.vertices i)
    (independent : ∀ i, G.IsIndepSet (I i : Set (Fin n)))
    (rounded : ∀ i, δ * k / (4 * n) < ∑ v ∈ P.vertices i, x v →
      (1 - δ) * (∑ v ∈ P.vertices i, x v) < targets i)
    (answers : ∀ i, δ * k / (4 * n) < ∑ v ∈ P.vertices i, x v →
      (1 - 4 * δ) ^ h * (targets i : ℝ) ≤ (I i).card) :
    G.IsIndepSet (combine I : Set (Fin n)) ∧
      (1 - 4 * δ) ^ (h + 1) * (k : ℝ) ≤ (combine I).card

end Lax263307.HeavyRecursiveRounding
