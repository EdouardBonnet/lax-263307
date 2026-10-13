import Lax263307.ProjectedOracle
import Lax263307.RelaxationFeasibility
import Lax263307Proofs.RationalProjection
import Mathlib.Tactic

namespace Lax263307Proofs.ProjectedOracle

open Matrix
open Lax263307.ProjectedOracle Lax263307.AlgorithmParameters
open Lax263307.LinearRelaxation Lax263307.MomentLP
open Lax109476.LinearProgram Lax109476.RationalCertificates

local notation "realQ" => Lax109476.RationalCertificates.realVector

theorem far_feasible {m N : ℕ} (P : Program ℚ m N) (x : Fin N → ℚ) (ρ : ℚ)
    (cert : Certificate (m+(N+N)) (N+1))
    (valid : IsValidCertificate (Lax263307.DistanceProjection.distanceProgram P x) cert)
    (normal : Fin N → ℚ) (α : ℚ)
    (far : Lax263307.RationalProjection.classify P ρ cert = .far normal α) :
    Lax109476.LinearProgram.IsFeasible (toReal P) := by
  cases cert with
  | infeasible dual => simp [Lax263307.RationalProjection.classify] at far
  | unbounded z direction => simp [Lax263307.RationalProjection.classify] at far
  | optimal z dual =>
    have hp := Lax263307Proofs.RationalProjection.primal_transfer _ z valid.1
    rw [Lax263307Proofs.RationalProjection.distance_cast] at hp
    exact ⟨Lax263307.DistanceProjection.point (realQ z),
      (Lax263307.DistanceProjection.primal_characterization _ _ _).mp hp |>.1⟩

theorem cast_raw {N : ℕ} (c : Fin N → ℚ) :
    realQ (raw c) = fun i => 4 * (N : ℝ) * (c i : ℝ) := by
  funext i
  simp [raw, Lax109476.RationalCertificates.realVector]

theorem tolerance_cast (a K B n D : ℕ) :
    (tolerance a K B n D : ℝ) = (momentFloor a K B n D : ℝ) *
      (1 / (D : ℝ)) ^ 2 / (32 * (n : ℝ)^2) := by
  simp only [tolerance, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
  ring

theorem cut_dot {n r : ℕ} (b : Coordinate n r → ℤ) (x : Index n r → ℝ) :
    (fun i => ((Lax263307.RoundedOracleSearch.rationalNormal (encode b) i : ℚ) : ℝ)) ⬝ᵥ x =
      Lax263307.ComponentCutEncoding.evaluate b (decode x) := by
  rw [Lax263307.MomentLP.evaluate_encoding]
  congr 1

theorem cut_norm {n r : ℕ} (b : Coordinate n r → ℤ) :
    (∑ i : Index n r, |((Lax263307.RoundedOracleSearch.rationalNormal (encode b) i : ℚ) : ℝ)|) =
      ∑ T, |(b T : ℝ)| := by
  simp only [Lax263307.RoundedOracleSearch.rationalNormal, Rat.cast_intCast, encode]
  exact Equiv.sum_comp (Lax263307.CoordinateCatalog.indexing n r) (fun T => |(b T : ℝ)|)

theorem run_correct {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k h : ℕ)
    (hK : 0 < K) (hn : 0 < n) (hD : 4 ≤ D)
    (lp_valid : ∀ (m N : ℕ) (P : Program ℚ m N), IsValidCertificate P (Lax263307.RegisteredLP.certificate lp P))
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n)))
    (near_correct : ∀ y : Lax263307.RationalConditioning.RationalVector n (level a K B n D),
      Lax263307.LinearRelaxation.IsFeasible G k (level a K B n D) (Lax263307.RationalConditioning.realVector y) →
      ∀ x : MomentVector n (level a K B n D),
      (∀ T, |x T - Lax263307.RationalConditioning.realVector y T| ≤ (momentFloor a K B n D : ℝ) *
        (1 / (D : ℝ))^2 / (32 * (n : ℝ)^2)) →
      Lax263307.NearOracle.Correct G k h D (momentFloor a K B n D) x
        (Lax263307.NearOracle.run flow a K B D G k y child))
    (center : Index n (level a K B n D) → ℚ) :
    Correct G k h a K B D center (run lp flow a K B D G k child center) := by
  let r := level a K B n D
  let N := dimension n r
  let P := program G k r
  let q := raw center
  let ρ := tolerance a K B n D
  let η : ℝ := momentFloor a K B n D
  let cert := Lax263307.RegisteredLP.certificate lp (Lax263307.DistanceProjection.distanceProgram P q)
  have hv := lp_valid _ _ (Lax263307.DistanceProjection.distanceProgram P q)
  have hc := Lax263307.RationalProjection.classify_correct P q ρ cert hv
  have hN : 0 < N := Lax263307.CoordinateCatalog.catalog_positive n r
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr (by omega)
  have hp : 0 < sparsity a K B n D := by
    dsimp [sparsity, targetThreshold]
    positivity
  have hη : 0 < η := by
    dsimp only [η]
    rw [conditioning_floor]
    unfold Lax263307.HeavyConditioning.probabilityFloor
    positivity
  have hρ : (0 : ℝ) < (ρ : ℝ) := by rw [tolerance_cast]; positivity
  have hprotect := (protected_radius (a:=a) (B:=B) hK hn (by omega : 0 < D)).2
  have hnear_radius : ((2 : ℝ)^precision a K B n D)⁻¹ ≤ (ρ : ℝ) / (8 * N) := by
    convert hprotect using 1
    dsimp [ρ, tolerance]
    push_cast
    ring
  dsimp only [run]
  cases hout : Lax263307.RationalProjection.classify P ρ cert with
  | reject =>
    rw [hout] at hc
    change independentSetHull G k r = ∅
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    apply hc
    refine ⟨encode z, (primal_characterization G k r (encode z)).mpr ?_⟩
    rw [decode_encode]
    exact Lax263307.RelaxationFeasibility.hull_feasible G k r z hz
  | far normal α =>
    rw [hout] at hc
    obtain ⟨hnorm, hvalid, hgap⟩ := hc
    obtain ⟨z, hz⟩ := far_feasible P q ρ cert hv normal α hout
    have hnz := Lax263307.RationalCutBuffer.normal_nonzero normal (realQ q) z (by
      have hh := hvalid z hz
      change (realQ normal) ⬝ᵥ z < (realQ normal) ⬝ᵥ (realQ q)
      dsimp [dotProduct, Lax109476.RationalCertificates.realVector] at *
      linarith only [hh, hgap, hρ])
    change (∃ i, _ ≠ 0) ∧ _
    refine ⟨hnz, ?_⟩
    intro z hz e he
    apply Lax263307.RationalCutBuffer.scaled_cleared_cut hN normal (realQ center) (encode z)
      (α : ℝ) (ρ : ℝ) ((ρ : ℝ)/2) 1 (by positivity) hnorm
    · apply hvalid
      apply (primal_characterization G k r _).mpr
      rw [decode_encode]
      exact Lax263307.RelaxationFeasibility.hull_feasible G k r z hz
    · have heq : (fun i => 4 * (N : ℝ) * (realQ center i)) = realQ q := (cast_raw center).symm
      rw [heq]
      change (α : ℝ) + (ρ : ℝ) ≤ ∑ i, (normal i : ℝ) * (q i : ℝ)
      linarith only [hgap]
    · simp
    · intro i
      have hh := (he i).trans hnear_radius
      rw [show (ρ : ℝ) / 2 / (4 * N) = (ρ : ℝ) / (8 * N) by ring]
      exact hh
  | near y =>
    rw [hout] at hc
    obtain ⟨hy, hclose⟩ := hc
    have hfeas : Lax263307.LinearRelaxation.IsFeasible G k r
        (Lax263307.RationalConditioning.realVector (decode y)) :=
      (primal_characterization G k r (realQ y)).mp hy
    have hclose' : ∀ T, |decode (realQ q) T - Lax263307.RationalConditioning.realVector (decode y) T| ≤
        η * (1 / (D : ℝ))^2 / (32 * (n : ℝ)^2) := by
      intro T
      have hh := hclose ((Lax263307.CoordinateCatalog.indexing n r).symm T)
      rw [abs_sub_comm] at hh
      change |decode (realQ q) T - Lax263307.RationalConditioning.realVector (decode y) T| ≤ (tolerance a K B n D : ℝ) at hh
      rw [tolerance_cast] at hh
      exact hh
    have ho := near_correct (decode y) hfeas (decode (realQ q)) hclose'
    dsimp only
    cases hresult : Lax263307.NearOracle.run flow a K B D G k (decode y) child with
    | reject => rw [hresult] at ho; exact False.elim ho
    | found I => rw [hresult] at ho; exact ho
    | cut A C u =>
      rw [hresult] at ho
      obtain ⟨_, _, _, hvalid, hgap, hnorm⟩ := ho
      let b := Lax263307.ComponentCutEncoding.coefficient (r:=r) A C u
      let normal := Lax263307.RoundedOracleSearch.rationalNormal (encode b)
      have hnorm' : (∑ i, |(normal i : ℝ)|) ≤ 2 * n := by rw [cut_norm]; exact hnorm
      have hgap' : η * (1/(D:ℝ))^2 / (16*n) ≤ (realQ normal) ⬝ᵥ realQ q := by
        change η * (1/(D:ℝ))^2 / (16*n) ≤ (fun i => (normal i : ℝ)) ⬝ᵥ realQ q
        rw [cut_dot]
        exact hgap
      have hnz := Lax263307.RationalCutBuffer.normal_nonzero normal (realQ q) 0 (by
        simp only [dotProduct_zero]
        exact lt_of_lt_of_le (by positivity) hgap')
      change (∃ i, _ ≠ 0) ∧ _
      refine ⟨hnz, ?_⟩
      intro z hz e he
      apply Lax263307.RationalCutBuffer.scaled_cleared_cut hN normal (realQ center) (encode z)
        0 (η * (1/(D:ℝ))^2 / (16*n)) ((ρ:ℝ)/2) (2*n) (by positivity) hnorm'
      · rw [cut_dot, decode_encode]
        exact hvalid z hz
      · have heq : (fun i => 4 * (N : ℝ) * (realQ center i)) = realQ q := (cast_raw center).symm
        rw [heq, zero_add]
        exact hgap'
      · dsimp only [ρ]
        rw [tolerance_cast]
        dsimp only [η]
        field_simp
        ring_nf
        exact le_rfl
      · intro i
        have hh := (he i).trans hnear_radius
        rw [show (ρ : ℝ) / 2 / (4 * N) = (ρ : ℝ) / (8 * N) by ring]
        exact hh


theorem search_correct {n : ℕ} (lp flow : List ℕ → List ℕ) (a K B D : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k h : ℕ)
    (hn : 0 < n) (hk : 0 < k)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n)))
    (oracle_correct : ∀ center, Correct G k h a K B D center (run lp flow a K B D G k child center)) :
    SearchCorrect G k h D (search lp flow a K B D G k child) := by
  let oracle := fun (_ : ℕ) center => run lp flow a K B D G k child center
  have hs : ∀ I, Lax263307.RoundedOracleSearch.search oracle (precision a K B n D) = some I → Good G k h D I := by
    apply Lax263307.RoundedOracleSearch.search_sound
    intro t center I he
    have hh := oracle_correct center
    change Correct G k h a K B D center (oracle t center) at hh
    rw [he] at hh
    exact hh
  cases hout : search lp flow a K B D G k child with
  | some I => exact hs I hout
  | none =>
    intro J _ hJ
    by_contra hlarge
    have hsize : k ≤ J.card := by omega
    obtain ⟨I, hIJ, hcard⟩ := Finset.exists_subset_card_eq hsize
    have hI : G.IsIndepSet (I : Set (Fin n)) := hJ.mono (by simpa using hIJ)
    have hmem : indicator (level a K B n D) I ∈ independentSetHull G k (level a K B n D) :=
      subset_convexHull ℝ _ ⟨I, hI, hcard, rfl⟩
    have hnz : ∀ t center normal, oracle t center = .cut normal → ∃ i, normal i ≠ 0 := by
      intro t center normal he
      have hh := oracle_correct center
      change Correct G k h a K B D center (oracle t center) at hh
      rw [he] at hh
      exact hh.1
    have hno : ∀ t center, oracle t center ≠ .reject := by
      intro t center he
      have hh := oracle_correct center
      change Correct G k h a K B D center (oracle t center) at hh
      rw [he] at hh
      change independentSetHull G k (level a K B n D) = ∅ at hh
      rw [hh] at hmem
      exact hmem
    have hretain : ∀ t center normal, oracle t center = .cut normal →
        ∀ e : Index n (level a K B n D) → ℝ,
        (∀ i, |e i| ≤ ((2 : ℝ)^precision a K B n D)⁻¹) →
        (fun i => (normal i : ℝ)) ⬝ᵥ
          (Lax263307.BufferedEllipsoid.scale (encode (indicator (level a K B n D) I)) + e -
            (fun i => (center i : ℝ))) ≤ 0 := by
      intro t center normal he e he'
      have hh := oracle_correct center
      change Correct G k h a K B D center (oracle t center) at hh
      rw [he] at hh
      exact hh.2 _ hmem e he'
    have hcube : ∀ i : Index n (level a K B n D),
        0 ≤ encode (indicator (level a K B n D) I) i ∧ encode (indicator (level a K B n D) I) i ≤ 1 := by
      intro i
      simp only [encode, indicator]
      split_ifs <;> norm_num
    obtain ⟨answer, hans⟩ := Lax263307.RoundedOracleSearch.search_complete
      (Lax263307.CoordinateCatalog.catalog_two n (level a K B n D) hn) oracle
      (precision a K B n D) (by unfold precision; omega) hnz hno _ hcube hretain
    change search lp flow a K B D G k child = some answer at hans
    rw [hout] at hans
    contradiction

open Lax263307.GraphClasses Lax263307.PowerBagBounds

/--
---
conclusion: Lax263307.ProjectedOracle.exists_search
---
A fixed pair of registered solvers supplies projection certificates and flow
cuts. The protected-cube argument proves completeness of the bounded search;
a size-k subset of any larger independent set excludes false rejection.
-/
theorem exists_search (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0 < a) (hA : 0 < A) (class_bound : HasPowerBagBound C a A) :
    ∃ (lp flow : List ℕ → List ℕ) (K B : ℕ),
      Lax759944.RamPolytime.RamPolytime lp ∧ Lax759944.RamPolytime.RamPolytime flow ∧
      0 < K ∧ 0 < B ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G ∈ C n → 0 < n → ∀ (D k h : ℕ), 4 ≤ D → cutoff a K B n D < k →
      ∀ (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))),
      Lax263307.NearOracle.ChildCorrect G D h child →
      SearchCorrect G k h D (search lp flow a K B D G k child) := by
  obtain ⟨lp, hpolyLP, hlp⟩ := Lax263307.RegisteredLP.exists_solver
  obtain ⟨flow, K, B, hpolyFlow, hK, hB, hnear⟩ :=
    Lax263307.NearOracle.exists_oracle C hereditary a A ha hA class_bound
  refine ⟨lp, flow, K, B, hpolyLP, hpolyFlow, hK, hB, ?_⟩
  intro n G _ hG hn D k h hD hlarge child hchild
  apply search_correct lp flow a K B D G k h hn (by omega) child
  intro center
  apply run_correct lp flow a K B D G k h hK hn hD hlp child
  intro y hy x hx
  exact hnear n G hG hn D k h hD hlarge y hy x hx child hchild

end Lax263307Proofs.ProjectedOracle
