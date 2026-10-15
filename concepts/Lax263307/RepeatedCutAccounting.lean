import Lax263307.PathSampling

/-!
---
title: Cumulative separator cost over disjoint discarded shores
type: lemma
---
Suppose repeated cuts of an $n$-vertex graph discard pairwise disjoint
shores $B_i$, and each separator $A_i\cap B_i$ has cost at most
$4\rho|A_i||B_i|/\gamma$. Nonnegative costs imply that the union of all
these separators has total cost at most $4\rho n^2/\gamma$.
The bound uses $|A_i|\le n$ and $\sum_i|B_i|\le n$.

# Attribution

Bonnet–Chang, the repeated-cut cost accounting in Lemma 8.
-/

namespace Lax263307.RepeatedCutAccounting

noncomputable def cost {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : ℝ := ∑ v ∈ S, x v

axiom total_cut_cost {n q : ℕ} (x : Fin n → ℝ) (nonnegative : ∀ v, 0 ≤ x v)
    (A B : Fin q → Finset (Fin n)) (disjoint : Pairwise fun i j => Disjoint (B i) (B j))
    (ρ γ : ℝ) (rho_nonnegative : 0 ≤ ρ) (gamma_positive : 0 < γ)
    (each_cut : ∀ i, cost x (A i ∩ B i) ≤ 4 * ρ * (A i).card * (B i).card / γ) :
    cost x (Finset.univ.biUnion fun i => A i ∩ B i) ≤ 4 * ρ * (n : ℝ) ^ 2 / γ

end Lax263307.RepeatedCutAccounting
