import Lax263307.ConditioningDistribution
import Lax263307.EntropyGap
import Lax263307Proofs.EntropyAlgebra

namespace Lax263307Proofs.EntropyDecrease

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution
open Lax263307.Entropy EntropyAlgebra

theorem adjacencyMass_div {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℝ) (k : ℝ) (hk : k ≠ 0) :
    adjacencyMass G (fun v => x v / k) = adjacencyMass G x / k ^ 2 := by
  unfold adjacencyMass
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs
  · field_simp
  · simp


end Lax263307Proofs.EntropyDecrease
