import Lax263307.HeavyRationalConditioning
import Lax263307Proofs.RationalConditioning
import Mathlib.Tactic

namespace Lax263307Proofs.HeavyRationalConditioning

open Lax263307.LinearRelaxation Lax263307.Entropy Lax263307.RationalConditioning
open Lax263307.HeavyConditioning Lax263307.HeavyRationalConditioning

theorem floor_cast (n p : ℕ) : (rationalFloor n p : ℝ) = probabilityFloor n p := by
  unfold rationalFloor probabilityFloor
  push_cast
  rfl

theorem heavy_passes_iff {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k p : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) (hp : 0 < p) :
    HeavyPasses G k p y A ↔ 0 < value (realVector y) A ∧
      edgeCost G (conditioned (realVector y) A) ≤ (k : ℝ) ^ 2 / p ∧
      probabilityFloor n p ^ r ≤ value (realVector y) A := by
  have hfloor : rationalFloor n p ^ r ≤ rationalValue y A ↔
      probabilityFloor n p ^ r ≤ value (realVector y) A := by
    rw [Lax263307Proofs.RationalConditioning.value_cast, ← floor_cast]
    norm_cast
  rw [HeavyPasses, Lax263307Proofs.RationalConditioning.passes_iff G k p y A hp, hfloor]
  tauto

/--
---
conclusion: Lax263307.HeavyRationalConditioning.search_correct
---
Cast the exact rational threshold and cleared edge test to their real
forms. Heavy conditioning supplies a candidate, and completeness puts
it in the enumerated list. The first successful candidate retains both
its raw moment floor and the conditioning invariants.
-/
theorem search_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k r p : ℕ) (y : RationalVector n r) (feasible : IsFeasible G k r (realVector y))
    (order_positive : 0 < n) (target_positive : 0 < k)
    (level_positive : 0 < r) (threshold_positive : 0 < p)
    (budget : (p : ℝ) * ((Nat.log2 n : ℝ) + 1) ≤ r) :
    ∃ A : Finset (Fin n), findHeavyConditioning G k p y = some A ∧ A.card ≤ r ∧
      probabilityFloor n p ^ r ≤ value (realVector y) A ∧ 0 < value (realVector y) A ∧
      (∀ v, 0 ≤ conditioned (realVector y) A v ∧ conditioned (realVector y) A v ≤ 1) ∧
      (∑ v, conditioned (realVector y) A v) = k ∧
      edgeCost G (conditioned (realVector y) A) ≤ (k : ℝ) ^ 2 / p := by
  obtain ⟨B, hB, hfloorB, hposB, _, _, heB⟩ := Lax263307.HeavyConditioning.heavy_low_edge_cost
    G k r p (realVector y) feasible order_positive target_positive level_positive threshold_positive budget
  have hpassB := (heavy_passes_iff G k p y B threshold_positive).mpr ⟨hposB, heB, hfloorB⟩
  have hmemB := (Lax263307.RationalConditioning.candidate_complete n r B).mpr hB
  cases hsearch : findHeavyConditioning G k p y with
  | none =>
    have hnone := List.find?_eq_none.mp hsearch B hmemB
    simp [hpassB] at hnone
  | some A =>
    have hpass : HeavyPasses G k p y A := by
      have h := List.find?_some hsearch
      simpa using h
    have hA := (Lax263307.RationalConditioning.candidate_complete n r A).mp
      (List.mem_of_find?_eq_some hsearch)
    have htest := (heavy_passes_iff G k p y A threshold_positive).mp hpass
    have h := Lax263307.ConditionedCosts.conditioning_invariants
      G k r (realVector y) feasible A hA htest.1
    exact ⟨A, rfl, hA, htest.2.2, htest.1, h.1, h.2.1, htest.2.1⟩

end Lax263307Proofs.HeavyRationalConditioning
