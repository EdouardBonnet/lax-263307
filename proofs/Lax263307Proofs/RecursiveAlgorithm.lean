import Lax263307.RecursiveAlgorithm
import Lax263307Proofs.ComputedSeparators
import Mathlib.Tactic

namespace Lax263307Proofs.RecursiveAlgorithm

open Lax263307.RecursiveAlgorithm Lax263307.ComputedSeparators
open Lax263307.GraphClasses Lax263307.AlgorithmParameters

theorem image_subset {n : ℕ} (C : Finset (Fin n)) (I : Finset (Fin C.card)) :
    I.image (label C) ⊆ C := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  exact C.orderEmbOfFin_mem rfl i

theorem image_independent {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n))
    (I : Finset (Fin C.card)) (hI : (restriction G C).IsIndepSet (I : Set (Fin C.card))) :
    G.IsIndepSet (I.image (label C) : Set (Fin n)) := by
  intro u hu v hv huv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  exact hI hi hj (fun hij => huv (congrArg (label C) hij))

theorem restriction_bound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) (t : ℕ)
    (hbound : ∀ I : Finset (Fin C.card), (restriction G C).IsIndepSet (I : Set (Fin C.card)) → I.card < t) :
    Lax263307.LinearRelaxation.IsIndependenceBound G C (t-1) := by
  intro J hJC hJ
  let I := Finset.univ.filter (fun i : Fin C.card => label C i ∈ J)
  have heq : I.image (label C) = J := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hi).2
    · intro hv
      have hcover : Finset.univ.image (label C) = C := Finset.image_orderEmbOfFin_univ C rfl
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hcover.symm ▸ hJC hv)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi ▸ hv⟩, hi⟩
  have hI : (restriction G C).IsIndepSet (I : Set (Fin C.card)) := by
    intro i hi j hj hij
    exact hJ (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
      ((label C).injective.ne hij)
  have hcard : I.card = J.card := by
    rw [← heq, Finset.card_image_of_injective _ (label C).injective]
  have hh := hbound I hI
  rw [hcard] at hh
  omega

theorem attempt_correct (C : GraphClass) (hereditary : IsHereditary C)
    (lp flow : List ℕ → List ℕ) (a K B D : ℕ) (hD : 4 ≤ D)
    (oracle : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ k h : ℕ, cutoff a K B n D < k →
      ∀ (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))),
      Lax263307.NearOracle.ChildCorrect G D h child →
      Lax263307.ProjectedOracle.SearchCorrect G k h D
        (Lax263307.ProjectedOracle.search lp flow a K B D G k child))
    (fuel : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G ∈ C n) (hdepth : Lax263307.RecursionDepth.depth n ≤ fuel) (k : ℕ) :
    Correct G k fuel D (attempt lp flow a K B D fuel G k) := by
  have hDpos : (0:ℝ) < D := Nat.cast_pos.mpr (by omega)
  have hβ : 0 ≤ 1 - 4*(1/(D:ℝ)) ∧ 1 - 4*(1/(D:ℝ)) ≤ 1 := by
    have hd : (4:ℝ) ≤ D := Nat.cast_le.mpr hD
    constructor
    · apply sub_nonneg.mpr
      rw [mul_one_div, div_le_one hDpos]
      exact hd
    · have : (0:ℝ) ≤ 4*(1/(D:ℝ)) := by positivity
      linarith
  induction fuel generalizing n k with
  | zero =>
    unfold attempt
    split_ifs with hsmall hlarge
    · have hh := Lax263307.ExhaustiveTargets.search_correct G k
      cases he : Lax263307.ExhaustiveTargets.findIndependentSet G k with
      | none => rw [he] at hh; exact hh
      | some I =>
        rw [he] at hh
        exact ⟨hh.1, by simp [hh.2]⟩
    · intro J _
      have hj : J.card ≤ n := by simpa using Finset.card_le_univ J
      omega
    · have hn : 1 < n := by omega
      rw [Lax263307.RecursionDepth.depth, if_neg (by omega)] at hdepth
      omega
  | succ fuel ih =>
    unfold attempt
    split_ifs with hsmall hlarge
    · have hh := Lax263307.ExhaustiveTargets.search_correct G k
      cases he : Lax263307.ExhaustiveTargets.findIndependentSet G k with
      | none => rw [he] at hh; exact hh
      | some I =>
        rw [he] at hh
        refine ⟨hh.1, ?_⟩
        have hp := pow_le_one₀ (n := fuel+1) hβ.1 hβ.2
        have hm := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg k : (0:ℝ) ≤ k)
        simpa [hh.2] using hm
    · intro J _
      have hj : J.card ≤ n := by simpa using Finset.card_le_univ J
      omega
    · have hn : 1 < n := by omega
      let child := fun (S : Finset (Fin n)) t =>
        (attempt lp flow a K B D fuel (restriction G S) t).map (fun I => I.image (label S))
      have hc : Lax263307.NearOracle.ChildCorrect G D fuel child := by
        intro S hS t
        have hclass := hereditary S.card n (restriction G S) G hG
          ⟨Lax263307Proofs.ComputedSeparators.embedding G S⟩
        have hdep := Lax263307.RecursionDepth.balanced_decrease n S.card hn hS
        have hh := ih (restriction G S) hclass (by omega) t
        dsimp only [child]
        cases he : attempt lp flow a K B D fuel (restriction G S) t with
        | some I =>
          rw [he] at hh
          change _ ∧ _ ∧ _
          refine ⟨image_subset S I, image_independent G S I hh.1, ?_⟩
          rw [Finset.card_image_of_injective _ (label S).injective]
          exact hh.2
        | none =>
          rw [he] at hh
          exact restriction_bound G S t hh
      have hh := oracle n G hG (by omega) k fuel (by omega) child hc
      change Correct G k (fuel+1) D (Lax263307.ProjectedOracle.search lp flow a K B D G k child)
      cases he : Lax263307.ProjectedOracle.search lp flow a K B D G k child with
      | some I =>
        rw [he] at hh
        exact hh
      | none =>
        rw [he] at hh
        intro J hJ
        have hb := hh J (Finset.subset_univ J) hJ
        have hk : 0 < k := by omega
        omega


theorem accuracy_budget (n : ℕ) (ε : ℚ) (hε : 0 < ε) :
    4 ≤ accuracyDenominator n ε ∧
      (Lax263307.RecursionDepth.depth n : ℚ) * (4 / accuracyDenominator n ε) ≤ ε := by
  let E := ⌈ε⁻¹⌉₊
  let d := Lax263307.RecursionDepth.depth n
  have hE : 0 < E := Nat.ceil_pos.mpr (inv_pos.mpr hε)
  have hEq : (0:ℚ) < E := Nat.cast_pos.mpr hE
  have hdq : (0:ℚ) < (d+1:ℕ) := Nat.cast_pos.mpr (by omega)
  have hD : 4 ≤ accuracyDenominator n ε := by
    change 4 ≤ 4 * (d+1) * E
    nlinarith only [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hE)]
  refine ⟨hD, ?_⟩
  have hceil : ε⁻¹ ≤ (E:ℚ) := Nat.le_ceil _
  have hprod : 1 ≤ ε * (E:ℚ) := by
    have hh := mul_le_mul_of_nonneg_left hceil hε.le
    simpa only [mul_inv_cancel₀ hε.ne'] using hh
  have hdiv : 1 / (E:ℚ) ≤ ε := (div_le_iff₀ hEq).mpr (by nlinarith only [hprod])
  apply le_trans _ hdiv
  change (d:ℚ) * (4 / (4 * (d+1) * E:ℕ)) ≤ 1 / (E:ℚ)
  push_cast
  apply (le_div_iff₀ hEq).mpr
  have hd : (0:ℚ) < (d:ℚ)+1 := by positivity
  field_simp
  ring_nf
  linarith

open Lax263307.PowerBagBounds

theorem independentSet_correct (C : GraphClass) (hereditary : IsHereditary C)
    (lp flow : List ℕ → List ℕ) (a K B : ℕ)
    (horacle : ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],G ∈ C n → 0<n →
      ∀ D k h,4≤D → cutoff a K B n D<k →
      ∀ child,Lax263307.NearOracle.ChildCorrect G D h child →
        Lax263307.ProjectedOracle.SearchCorrect G k h D
          (Lax263307.ProjectedOracle.search lp flow a K B D G k child))
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G ∈ C n)
    (ε : ℚ) (hε : 0<ε) (hεsmall : ε<1) :
    Lax263307.WeightedIndependentSet.IsApproximation G (fun _ => 1) ε
      (independentSet lp flow a K B G ε) := by
  let D := accuracyDenominator n ε
  let depth := Lax263307.RecursionDepth.depth n
  have hD := (accuracy_budget n ε hε).1
  have hcorrect (k : ℕ) := attempt_correct C hereditary lp flow a K B D hD
    (fun n G _ hG hn k h hlarge child hc => horacle n G hG hn D k h hD hlarge child hc)
    depth G hG le_rfl k
  have hsuccess : ∀ k, k ≤ n → ∀ I, attempt lp flow a K B D depth G k = some I →
      G.IsIndepSet (I : Set (Fin n)) ∧ (1-4*(1/(D:ℝ)))^depth * (k:ℝ) ≤ I.card := by
    intro k _ I he
    have hh := hcorrect k
    rw [he] at hh
    exact hh
  have hfailure : ∀ k, 0 < k → k ≤ n → attempt lp flow a K B D depth G k = none →
      ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card < k := by
    intro k _ _ he
    have hh := hcorrect k
    rw [he] at hh
    exact hh
  have hs := Lax263307.TargetSearch.search_correct G ((1-4*(1/(D:ℝ)))^depth)
    (attempt lp flow a K B D depth G) hsuccess hfailure
  change _ ∧ _ ∧ _ ∧ _ at hs
  let result := solve lp flow a K B D G
  have hind : G.IsIndepSet (result.1 : Set (Fin n)) := hs.1
  have hu : ∀ J : Finset (Fin n), G.IsIndepSet (J : Set (Fin n)) → J.card ≤ result.2 := hs.2.1
  have hsize : (1-(4/(D:ℚ)))^depth * (result.2:ℚ) ≤ result.1.card := by
    have hr : (1-4*(1/(D:ℝ)))^depth * (result.2:ℝ) ≤ result.1.card := hs.2.2.2
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    simpa only [mul_one_div] using hr
  apply Lax263307.RecursionDepth.approximation_transfer G result.1 result.2 depth (4/(D:ℚ)) ε
    hind hu (by positivity) _ hεsmall.le (accuracy_budget n ε hε).2 hsize
  have hDq : (4:ℚ) ≤ D := Nat.cast_le.mpr hD
  have hDpos : (0:ℚ) < D := Nat.cast_pos.mpr (by omega)
  exact (div_le_one hDpos).mpr hDq


end Lax263307Proofs.RecursiveAlgorithm
