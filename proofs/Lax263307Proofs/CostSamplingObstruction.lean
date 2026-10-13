import Lax263307.CostSamplingObstruction
import Mathlib.Tactic

namespace Lax263307Proofs.CostSamplingObstruction

open Lax263307.GraphClasses Lax263307.InducedEmbeddingWidth Lax228581.Treewidth

theorem sufficient_budget (m ℓ k p : ℝ) (k_positive : 0 < k) (p_positive : 0 < p)
    (hk : 8 * m ^ 2 * ℓ ^ 2 ≤ k) (hp : 16 * m ^ 2 * ℓ ^ 2 ≤ p) :
    m ^ 2 * (ℓ ^ 2 / k + 2 * ℓ ^ 2 / p) ≤ 1 / 4 := by
  have h₁ : m ^ 2 * ℓ ^ 2 / k ≤ 1 / 8 := (div_le_iff₀ k_positive).mpr (by nlinarith)
  have h₂ : 2 * m ^ 2 * ℓ ^ 2 / p ≤ 1 / 8 := (div_le_iff₀ p_positive).mpr (by nlinarith)
  calc
    m ^ 2 * (ℓ ^ 2 / k + 2 * ℓ ^ 2 / p) = m ^ 2 * ℓ ^ 2 / k + 2 * m ^ 2 * ℓ ^ 2 / p := by ring
    _ ≤ 1 / 8 + 1 / 8 := add_le_add h₁ h₂
    _ = 1 / 4 := by norm_num

/--
---
conclusion: Lax263307.CostSamplingObstruction.cost_width_obstruction
---
Apply the three cost-based sampling estimates. The target and sparsity
thresholds bound the two interaction contributions by 1/8 each. The
expected total route size is at most m*ell, which is positive. Invoke the
proved sampled width obstruction with this value of M.
-/
theorem cost_width_obstruction {t n q : ℕ} (C : GraphClass) (hereditary : IsHereditary C)
    (W : ℕ → ℕ) (monotone : Monotone W) (class_bound : HasBagBound C W)
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (member : G ∈ C n) (D : Lax263307.RouteDistributions.Distribution G q) (hn : 0 < n)
    (d L : ℕ) (degree_bound : ∀ v, H.degree v ≤ d) (edge_positive : 0 < H.edgeSet.ncard)
    (x : Fin n → ℝ) (k ℓ p : ℝ) (k_positive : 0 < k) (ℓ_positive : 0 < ℓ) (p_positive : 0 < p)
    (cost_bounds : ∀ v, 0 ≤ x v ∧ x v ≤ 1) (mass : (∑ v, x v) ≤ k)
    (load_bound : ∀ v, Lax263307.PathSampling.load D.toSampling v ≤ ℓ * x v / k)
    (edge_bound : Lax263307.Entropy.edgeCost G x ≤ k ^ 2 / p)
    (target_large : 8 * (H.edgeSet.ncard : ℝ) ^ 2 * ℓ ^ 2 ≤ k)
    (sparsity_large : 16 * (H.edgeSet.ncard : ℝ) ^ 2 * ℓ ^ 2 ≤ p) :
    ∃ removed : ℕ, (L : ℝ) * removed ≤ 4 * (H.edgeSet.ncard : ℝ) * ℓ ∧
      treewidth H + 1 ≤ max 1 (2 * d * W (d * H.edgeSet.ncard * L ^ 2)) + removed := by
  classical
  obtain ⟨hcoll, hadj, hsize⟩ := Lax263307.PathSampling.sampling_bounds G D.toSampling x k ℓ p
    k_positive ℓ_positive.le p_positive cost_bounds mass load_bound edge_bound
  have hbad : (H.edgeSet.ncard : ℝ) ^ 2 * (Lax263307.PathSampling.collisionProbability D.toSampling +
      Lax263307.PathSampling.adjacencyProbability G D.toSampling) ≤ 1 / 4 := by
    apply le_trans (mul_le_mul_of_nonneg_left (add_le_add hcoll hadj) (sq_nonneg _))
    exact sufficient_budget _ ℓ k p k_positive p_positive target_large sparsity_large
  have hM : 0 < (H.edgeSet.ncard : ℝ) * ℓ := mul_pos (by exact_mod_cast edge_positive) ℓ_positive
  have hlen := mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg H.edgeSet.ncard : (0 : ℝ) ≤ _)
  obtain ⟨removed, hremoved, hwidth⟩ := Lax263307.InducedEmbeddingWidth.sampled_width_bound C hereditary
    W monotone class_bound H G member D hn d L degree_bound _ hM hbad hlen
  exact ⟨removed, by simpa only [mul_assoc] using hremoved, hwidth⟩


end Lax263307Proofs.CostSamplingObstruction
