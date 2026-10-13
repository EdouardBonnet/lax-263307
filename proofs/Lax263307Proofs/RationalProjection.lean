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

theorem old_multipliers_cast {m n : ℕ} (dual : Fin (m + (n + n)) → ℚ) :
    oldMultipliers (realVector dual) = realVector (oldMultipliers dual) := rfl

/--
---
conclusion: Lax263307.RationalProjection.certificate_outcome
---
-/
theorem certificate_outcome {m n : ℕ} (P : Program ℚ m n) (center : Fin n → ℚ)
    (certificate : Certificate (m + (n + n)) (n + 1))
    (valid : IsValidCertificate (distanceProgram P center) certificate) (ρ : ℝ) :
    (¬ IsFeasible (toReal P)) ∨
      (∃ y : Fin n → ℚ, PrimalFeasible (toReal P) (realVector y) ∧
        ∀ j, |(y j : ℝ) - (center j : ℝ)| ≤ ρ) ∨
      (∃ a : Fin n → ℚ, ∃ α : ℚ,
        (∑ j, |(a j : ℝ)|) ≤ 1 ∧
        (∀ y, PrimalFeasible (toReal P) y → (∑ j, (a j : ℝ) * y j) ≤ (α : ℝ)) ∧
        ρ < (∑ j, (a j : ℝ) * (center j : ℝ)) - (α : ℝ)) := by
  cases certificate with
  | optimal z dual =>
    obtain ⟨primal, dual_feasible, matching⟩ := valid
    have hp := primal_transfer (distanceProgram P center) z primal
    have hd := dual_transfer (distanceProgram P center) dual dual_feasible
    rw [distance_cast] at hp hd
    have hm : primalValue (distanceProgram (toReal P) (realVector center)) (realVector z) =
        dualValue (distanceProgram (toReal P) (realVector center)) (realVector dual) := by
      rw [← distance_cast, cast_primal_value, cast_dual_value, matching]
    obtain hnear | hfar := Lax263307.DistanceProjection.strong_gap_dichotomy
      (toReal P) (realVector center) (realVector z) (realVector dual) hp hd hm ρ
    · exact Or.inr (Or.inl ⟨point z, hnear⟩)
    · right; right
      refine ⟨normal dual, dualValue P (oldMultipliers dual), ?_⟩
      simpa only [normal_cast, old_multipliers_cast, cast_dual_value, realVector] using hfar
  | infeasible dual =>
    have hbad := Lax109476.CertificateSoundness.valid_certificate_correct _ _
      (distanceProgram P center) (.infeasible dual) valid
    change ¬ IsFeasible (toReal (distanceProgram P center)) at hbad
    rw [distance_cast, Lax263307.DistanceProjection.projection_feasible_iff] at hbad
    exact Or.inl hbad
  | unbounded z direction =>
    have hbad := Lax109476.CertificateSoundness.valid_certificate_correct _ _
      (distanceProgram P center) (.unbounded z direction) valid
    change IsFeasible (toReal (distanceProgram P center)) ∧
      ¬ IsBoundedAbove (toReal (distanceProgram P center)) at hbad
    rw [distance_cast] at hbad
    exact False.elim (hbad.2 (Lax263307.DistanceProjection.objective_bounded
      (toReal P) (realVector center)))

end Lax263307Proofs.RationalProjection
