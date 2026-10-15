import Lax263307.ConditioningDistribution
import Lax263307.EntropyGap
import Lax263307.EntropyBounds
import Lax263307Proofs.EntropyAlgebra
import Lax263307Proofs.RelaxationAlgebra

namespace Lax263307Proofs.ConditioningExistence

open Lax263307.LinearRelaxation Lax263307.ConditioningDistribution Lax263307.Entropy
open EntropyAlgebra RelaxationAlgebra

theorem marginal_probability {n : ℕ} (G : SimpleGraph (Fin n)) (k r : ℕ)
    (y : MomentVector n r) (hy : IsFeasible G k r y)
    (A : Finset (Fin n)) (hA : A.card ≤ r) (hpos : 0 < value y A) (hk : 0 < k) :
    IsProbability (marginal y A k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := Lax263307.ConditionedCosts.conditioning_invariants G k r y hy A hA hpos
  refine ⟨fun v => div_nonneg (h.1 v).1 hkR.le, ?_⟩
  simp_rw [marginal, ← Finset.sum_div]
  rw [h.2.1, div_self (ne_of_gt hkR)]


end Lax263307Proofs.ConditioningExistence
