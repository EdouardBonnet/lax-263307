import Lax263307.RoundedOracleSearch
import Lax109476Proofs.EllipsoidTermination
import Lax109476Proofs.EllipsoidStateSize
import Mathlib.Tactic

namespace Lax263307Proofs.RoundedOracleSearch

open Matrix Lax263307.RoundedOracleSearch
open Lax109476.RationalCertificates

theorem cached_eq {n : ℕ} (state : State n) : cached state = state := by
  apply Prod.ext
  · funext i j
    simp [cached, Vector.get]
    rfl
  · funext i
    simp [cached, Vector.get]
    rfl

theorem scan_sound {n : ℕ} {Result : Type}
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result) (Good : Result → Prop)
    (answers : ∀ k center answer, oracle k center = .found answer → Good answer)
    (count k : ℕ) (state : State n) (answer : Result)
    (found : scan oracle k count state = some answer) : Good answer := by
  induction count generalizing k state with
  | zero => simp [scan] at found
  | succ count ih =>
    cases hreply : oracle k state.2 with
    | found result =>
      have heq : result = answer := by simpa only [scan, hreply, Option.some.injEq] using found
      subst answer
      exact answers k state.2 result hreply
    | reject => simp [scan, hreply] at found
    | cut a =>
      apply ih (k + 1) (update k state a)
      simpa only [scan, hreply] using found

/--
---
conclusion: Lax263307.RoundedOracleSearch.search_sound
---
The bounded scan returns only an answer produced by an oracle call.
-/
theorem search_sound {n : ℕ} {Result : Type}
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result) (B : ℕ) (Good : Result → Prop)
    (answers : ∀ k center answer, oracle k center = .found answer → Good answer) :
    ∀ answer, search oracle B = some answer → Good answer := by
  intro answer found
  exact scan_sound oracle Good answers (steps n B) 0 (1, 0) answer found

theorem scan_failure {n : ℕ} {Result : Type}
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (no_reject : ∀ k center, oracle k center ≠ .reject) (count k : ℕ)
    (failed : scan oracle k count (trajectory oracle k) = none) :
    ∀ j, k ≤ j → j < k + count → ∃ a, oracle j (trajectory oracle j).2 = .cut a := by
  induction count generalizing k with
  | zero => intro j hj hj'; omega
  | succ count ih =>
    cases hreply : oracle k (trajectory oracle k).2 with
    | found answer => simp [scan, hreply] at failed
    | reject => exact False.elim (no_reject k _ hreply)
    | cut a =>
      have hnext : trajectory oracle (k + 1) = update k (trajectory oracle k) a := by
        simp only [trajectory, hreply, selectedNormal]
      have htail : scan oracle (k + 1) count (trajectory oracle (k + 1)) = none := by
        rw [hnext]
        simpa only [scan, hreply] using failed
      intro j hj hj'
      by_cases heq : j = k
      · subst j
        exact ⟨a, hreply⟩
      · exact ih (k + 1) htail j (by omega) (by omega)

theorem schedule_norm {n : ℕ} {Result : Type} (positive : 0 < n)
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (nonzero : ∀ k center a, oracle k center = .cut a → ∃ i, a i ≠ 0) (k : ℕ) :
    1 ≤ realVector (rationalNormal (normalSchedule oracle k)) ⬝ᵥ
      realVector (rationalNormal (normalSchedule oracle k)) := by
  have hnormal : ∃ i, normalSchedule oracle k i ≠ 0 := by
    unfold normalSchedule
    cases hreply : oracle k (trajectory oracle k).2 with
    | cut a => exact nonzero k _ a hreply
    | found answer => exact ⟨⟨0, positive⟩, by simp [selectedNormal, fallback]⟩
    | reject => exact ⟨⟨0, positive⟩, by simp [selectedNormal, fallback]⟩
  have hcast : realVector (rationalNormal (normalSchedule oracle k)) =
      (fun i => (normalSchedule oracle k i : ℝ)) := by
    funext i
    simp [realVector, rationalNormal]
  rw [hcast]
  exact Lax263307.BufferedEllipsoid.integer_normal_norm (normalSchedule oracle k) hnormal

theorem trajectory_eq_sequences {n : ℕ} {Result : Type}
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result) (k : ℕ) :
    (trajectory oracle k).1 = Lax109476Proofs.EllipsoidSequence.shapes n
      (fun j => rationalNormal (normalSchedule oracle j)) k ∧
    (trajectory oracle k).2 = Lax109476Proofs.EllipsoidSequence.centers n
      (fun j => rationalNormal (normalSchedule oracle j)) 0 k := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    change (update k (trajectory oracle k) (normalSchedule oracle k)).1 = _ ∧
      (update k (trajectory oracle k) (normalSchedule oracle k)).2 = _
    simp only [update, cached_eq]
    change Lax109476Proofs.EllipsoidCenter.roundedStepShape n (trajectory oracle k).1
        (rationalNormal (normalSchedule oracle k))
        (Lax109476Proofs.EllipsoidPrecision.gridDenominator (2 * k + 2) (2 * n + 4) n)
        (Lax109476Proofs.EllipsoidIteration.stepAccuracy n) = _ ∧
      Lax109476Proofs.EllipsoidCenter.roundedCenter n (trajectory oracle k).1
        (rationalNormal (normalSchedule oracle k)) (trajectory oracle k).2
        (Lax109476Proofs.EllipsoidPrecision.gridDenominator (2 * k + 2) (2 * n + 4) n) = _
    simp only [Lax109476Proofs.EllipsoidSequence.shapes, Lax109476Proofs.EllipsoidSequence.centers]
    rw [ih.1, ih.2]
    exact ⟨rfl, rfl⟩

/--
---
conclusion: Lax263307.RoundedOracleSearch.search_complete
---
Failure without an immediate rejection means every tested center returned a cut.
Those cuts retain the protected ball, contradicting the registered rounded
sequence's determinant decrease at the explicit iteration budget.
-/
theorem search_complete {n : ℕ} {Result : Type} (dimension : 2 ≤ n)
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result) (B : ℕ) (precision : 2 ≤ B)
    (nonzero : ∀ k center a, oracle k center = .cut a → ∃ i, a i ≠ 0)
    (no_reject : ∀ k center, oracle k center ≠ .reject)
    (z : Fin n → ℝ) (cube : ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (retains : ∀ k center a, oracle k center = .cut a →
      ∀ e : Fin n → ℝ, (∀ i, |e i| ≤ ((2 : ℝ) ^ B)⁻¹) →
        (fun i => (a i : ℝ)) ⬝ᵥ
          (Lax263307.BufferedEllipsoid.scale z + e - (fun i => (center i : ℝ))) ≤ 0) :
    ∃ answer, search oracle B = some answer := by
  by_contra hfound
  have hnone : search oracle B = none := by
    cases h : search oracle B with
    | none => rfl
    | some answer => exact False.elim (hfound ⟨answer, h⟩)
  have hcuts := scan_failure oracle no_reject (steps n B) 0 hnone
  let a : ℕ → Fin n → ℚ := fun k => rationalNormal (normalSchedule oracle k)
  let ρ : ℝ := ((2 : ℝ) ^ B)⁻¹
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hsmall : ρ ≤ 1 / 4 := by
    have hp : (4 : ℝ) ≤ (2 : ℝ) ^ B := by
      have h := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) precision
      norm_num at h
      exact h
    dsimp [ρ]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hp
  apply Lax109476Proofs.EllipsoidTermination.cannot_retain_ball n dimension a
    (fun k => schedule_norm (by omega) oracle nonzero k) 0
    (Lax263307.BufferedEllipsoid.scale z) B
  · intro e he
    have h := Lax263307.BufferedEllipsoid.initial_ball (by omega) z cube ρ hρ hsmall e he
    have hzero : realVector (0 : Fin n → ℚ) = 0 := by funext i; simp [realVector]
    rw [hzero]
    simpa only [sub_zero] using h
  · intro k hk e he
    obtain ⟨normal, hreply⟩ := hcuts k (by omega)
      (by simpa only [Lax109476Proofs.EllipsoidSequence.thresholdSteps, steps, Nat.zero_add] using hk)
    have hnormal : a k = rationalNormal normal := by
      simp only [a, normalSchedule, hreply, selectedNormal]
    rw [hnormal]
    have h := retains k (trajectory oracle k).2 normal hreply e
      (Lax263307.BufferedEllipsoid.coordinate_ball_bound e ρ hρ he)
    rw [(trajectory_eq_sequences oracle k).2] at h
    have hcast : realVector (rationalNormal normal) = (fun i => (normal i : ℝ)) := by
      funext i
      simp [realVector, rationalNormal]
    rw [hcast]
    exact h

/--
---
conclusion: Lax263307.RoundedOracleSearch.center_encoding_bound
---
Identify the stored center with the registered sequence. Its grid and
magnitude bounds give a linear encoding bound independent of incoming normals.
-/
theorem center_encoding_bound {n : ℕ} {Result : Type} (dimension : 2 ≤ n)
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (nonzero : ∀ k center a, oracle k center = .cut a → ∃ i, a i ≠ 0) (k : ℕ) (i : Fin n) :
    Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeRational ((trajectory oracle k).2 i)) ≤ 60 + 6 * k + 14 * n := by
  rw [(trajectory_eq_sequences oracle k).2]
  exact Lax109476Proofs.EllipsoidStateSize.centers_encoding_size n dimension
    (fun j => rationalNormal (normalSchedule oracle j))
    (fun j => schedule_norm (by omega) oracle nonzero j) k i

/--
---
conclusion: Lax263307.RoundedOracleSearch.shape_encoding_bound
---
The registered rounded shape uses a fixed grid and has a bounded magnitude;
its stored entries satisfy the same linear encoding bound as the center.
-/
theorem shape_encoding_bound {n : ℕ} {Result : Type} (dimension : 2 ≤ n)
    (oracle : ℕ → (Fin n → ℚ) → Reply n Result)
    (nonzero : ∀ k center a, oracle k center = .cut a → ∃ i, a i ≠ 0)
    (k : ℕ) (i j : Fin n) :
    Lax759944.BinaryWordEncoding.bitSize
      (Lax109476.RationalEncoding.encodeRational ((trajectory oracle k).1 i j)) ≤ 60 + 6 * k + 14 * n := by
  rw [(trajectory_eq_sequences oracle k).1]
  exact Lax109476Proofs.EllipsoidStateSize.shapes_encoding_size n dimension
    (fun j => rationalNormal (normalSchedule oracle j))
    (fun j => schedule_norm (by omega) oracle nonzero j) k i j

end Lax263307Proofs.RoundedOracleSearch
