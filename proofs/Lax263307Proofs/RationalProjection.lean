import Lax263307.RationalProjection
import Lax263307.DistanceProjection
import Mathlib.Tactic

namespace Lax263307Proofs.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax263307.DistanceProjection

theorem cast_row {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (i : Fin m) :
    rowValue (toReal P) (realVector x) i = ((rowValue P x i : ℚ) : ℝ) := by
  unfold rowValue toReal realVector
  push_cast
  rfl

theorem cast_column {m n : ℕ} (P : Program ℚ m n) (x : Fin m → ℚ) (j : Fin n) :
    columnValue (toReal P) (realVector x) j = ((columnValue P x j : ℚ) : ℝ) := by
  unfold columnValue toReal realVector
  push_cast
  rfl

theorem cast_primal_value {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) :
    primalValue (toReal P) (realVector x) = ((primalValue P x : ℚ) : ℝ) := by
  unfold primalValue toReal realVector
  push_cast
  rfl

theorem cast_dual_value {m n : ℕ} (P : Program ℚ m n) (x : Fin m → ℚ) :
    dualValue (toReal P) (realVector x) = ((dualValue P x : ℚ) : ℝ) := by
  unfold dualValue toReal realVector
  push_cast
  rfl

theorem primal_transfer {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (feasible : PrimalFeasible P x) :
    PrimalFeasible (toReal P) (realVector x) := by
  constructor
  · intro j
    change (0 : ℝ) ≤ (x j : ℝ)
    exact_mod_cast feasible.1 j
  · intro i
    rw [cast_row]
    change ((rowValue P x i : ℚ) : ℝ) ≤ (P.b i : ℝ)
    exact_mod_cast feasible.2 i

theorem dual_transfer {m n : ℕ} (P : Program ℚ m n) (x : Fin m → ℚ) (feasible : DualFeasible P x) :
    DualFeasible (toReal P) (realVector x) := by
  constructor
  · intro i
    change (0 : ℝ) ≤ (x i : ℝ)
    exact_mod_cast feasible.1 i
  · intro j
    rw [cast_column]
    change (P.c j : ℝ) ≤ ((columnValue P x j : ℚ) : ℝ)
    exact_mod_cast feasible.2 j

theorem distance_cast {m n : ℕ} (P : Program ℚ m n) (center : Fin n → ℚ) :
    toReal (distanceProgram P center) = distanceProgram (toReal P) (realVector center) := by
  unfold toReal distanceProgram
  congr 1
  · funext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.addCases_left]
      · simp
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp only [Fin.addCases_left, Fin.addCases_right] <;> first | rfl | simp [apply_ite]
      · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp only [Fin.addCases_left, Fin.addCases_right] <;> first | rfl | simp [apply_ite]
  · funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.addCases_left]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> (simp only [Fin.addCases_left, Fin.addCases_right]; simp [realVector])
  · funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp only [Fin.addCases_left, Fin.addCases_right] <;> norm_num

theorem normal_cast {m n : ℕ} (dual : Fin (m + (n + n)) → ℚ) :
    normal (realVector dual) = fun j => ((normal dual j : ℚ) : ℝ) := by
  funext j
  simp [normal, plusMultipliers, minusMultipliers, realVector]

/--
---
conclusion: Lax263307.RationalProjection.classify_correct
---
The branch test uses the distance coordinate in the actual optimal certificate.
The matching dual gives that exact gap. Infeasible and unbounded certificates
are handled using the registered certificate soundness theorem.
-/
theorem classify_correct {m n : ℕ} (P : Program ℚ m n) (center : Fin n → ℚ) (ρ : ℚ)
    (certificate : Certificate (m + (n + n)) (n + 1))
    (valid : IsValidCertificate (distanceProgram P center) certificate) :
    Lax263307.RationalProjection.Correct P center ρ
      (Lax263307.RationalProjection.classify P ρ certificate) := by
  cases certificate with
  | optimal z dual =>
    obtain ⟨primal, dual_feasible, matching⟩ := valid
    have hp := primal_transfer (distanceProgram P center) z primal
    have hd := dual_transfer (distanceProgram P center) dual dual_feasible
    rw [distance_cast] at hp hd
    have hm : primalValue (distanceProgram (toReal P) (realVector center)) (realVector z) =
        dualValue (distanceProgram (toReal P) (realVector center)) (realVector dual) := by
      rw [← distance_cast, cast_primal_value, cast_dual_value, matching]
    have hg := Lax263307.DistanceProjection.optimal_gap
      (toReal P) (realVector center) (realVector z) (realVector dual) hp hd hm
    have hdistance : distance (realVector z) = ((distance z : ℚ) : ℝ) := rfl
    have hpoint : point (realVector z) = realVector (point z) := rfl
    have hold : oldMultipliers (realVector dual) = realVector (oldMultipliers dual) := rfl
    simp only [Lax263307.RationalProjection.classify]
    split_ifs with hnear
    · change PrimalFeasible (toReal P) (realVector (point z)) ∧ _
      refine ⟨by simpa only [hpoint] using hg.1, ?_⟩
      intro j
      have hdist : ((distance z : ℚ) : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hnear
      exact (hg.2.2.1 j).trans hdist
    · change (∑ j, |((normal dual j : ℚ) : ℝ)|) ≤ 1 ∧ _
      have hfar : (ρ : ℝ) < ((distance z : ℚ) : ℝ) := by
        exact_mod_cast (lt_of_not_ge hnear)
      have hgap := hg.2.2.2.2.2
      rw [normal_cast, hold, cast_dual_value, hdistance] at hgap
      refine ⟨?_, ?_, ?_⟩
      · simpa only [normal_cast] using hg.2.2.2.1
      · simpa only [normal_cast, hold, cast_dual_value] using hg.2.2.2.2.1
      · simpa only [← hgap, realVector] using hfar
  | infeasible dual =>
    have hbad := Lax109476.CertificateSoundness.valid_certificate_correct _ _
      (distanceProgram P center) (.infeasible dual) valid
    change ¬ IsFeasible (toReal (distanceProgram P center)) at hbad
    rw [distance_cast, Lax263307.DistanceProjection.projection_feasible_iff] at hbad
    exact hbad
  | unbounded z direction =>
    have hbad := Lax109476.CertificateSoundness.valid_certificate_correct _ _
      (distanceProgram P center) (.unbounded z direction) valid
    change IsFeasible (toReal (distanceProgram P center)) ∧
      ¬ IsBoundedAbove (toReal (distanceProgram P center)) at hbad
    rw [distance_cast] at hbad
    exact False.elim (hbad.2 (Lax263307.DistanceProjection.objective_bounded
      (toReal P) (realVector center)))


end Lax263307Proofs.RationalProjection
