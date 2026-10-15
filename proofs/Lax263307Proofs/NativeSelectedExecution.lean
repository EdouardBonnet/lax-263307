import Lax263307Proofs.NativeRootWorkspace
import Lax263307Proofs.NativeLocalTime

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedExecution

open Lax263307 GraphClasses AlgorithmParameters
open NativeCoreMachine NativeRootWorkspace NativeSelectedRounds

abbrev domain (C : GraphClass) (cfg : Config) (rootN W : ℕ) :=
  NativeRecursiveDomain.eligible C rootN (frameLength cfg W) (capacity cfg rootN W)

theorem fuel_bound {C : GraphClass} {cfg : Config} {rootN W fuel n k cursor : ℕ} {G : SimpleGraph (Fin n)}
    (hi : domain C cfg rootN W fuel n G k cursor) : fuel ≤ RecursionDepth.depth rootN := by
  have h := hi.2.2.2.2.2.2
  dsimp only [capacity] at h
  exact Nat.le_of_mul_le_mul_right (by omega : fuel*frameLength cfg W ≤ RecursionDepth.depth rootN*frameLength cfg W)
    (frame_positive cfg W)

/-- Construct the complete resource record used by the checked fuel
induction. No phase, oracle, round, or child execution is assumed. -/
noncomputable def resources {C : GraphClass} (hereditary : IsHereditary C)
    {lp flow : List ℕ → List ℕ} (p : NativeSelectedLP.Program lp) (q : NativeSelectedNear.Program flow)
    (cfg : Config) (hpc : p.code=cfg.lp) (hpcoeff : p.coeff=cfg.lpWidth)
    (hqc : q.code=cfg.flow) (hqcoeff : q.coeff=cfg.flowWidth)
    (encoded : NativeEncodedLP.Encoded lp) (hsep : NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b)
    (correct : NativeRecursiveOracle.OracleCorrect C lp flow cfg.a cfg.K cfg.b) (hK : 0<cfg.K) (hb : 0<cfg.b)
    (D c rootN originalN R W w : ℕ) (hD : 4 ≤ D) (hroot : rootN ≤ R)
    (program : NativeOracleRounds.Program cfg.rounded c)
    (uniform : ∀ n,0<n → n ≤ rootN → ParameterResources.resource cfg.a cfg.K cfg.b n D ≤ R)
    (budget : NativeSelectedBudget.demand cfg p q c R ≤ W) (host : hostHeight cfg W ≤ w) :
    NativeNodeExecution.Resources D (stride W) W w (NativeLocalTime.steps W)
      (NativeLocalTime.time cfg W (stride W)) (NativeLocalTime.branches W) cfg lp flow
      (extent cfg rootN W originalN) (domain C cfg rootN W) := by
  have hdem := budget
  dsimp only [NativeSelectedBudget.demand] at hdem
  have hR : R ≤ W := by omega
  have hhost : W ≤ w := by dsimp only [hostHeight] at host; omega
  have rootDepth : RecursionDepth.depth rootN ≤ 2*R+2 := by
    have h := RecursionDepth.logarithmic_bound rootN
    have hl := Nat.log2_le_self rootN
    omega
  refine ⟨frame_extents cfg rootN W originalN,?_,?_,?_,?_⟩
  · intro fuel n G _ k cursor hi
    have hres := uniform n hi.2.1 hi.2.2.1
    exact NativeEntryResources.bounds cfg n D k fuel R w (extent cfg rootN W originalN) hK hi.2.1 (by omega)
      hi.2.2.2.2.1 ((fuel_bound hi).trans rootDepth) hres
      ((by omega : NativeEntryResources.amount cfg R ≤ W).trans hhost)
      (buffer_room cfg rootN W originalN _ NativeEntryResources.buffers (by simp [List.disjoint_left,NativeEntryResources.buffers]) (by omega))
  · intro fuel n G _ k cursor hi
    have hnW : n ≤ W := hi.2.2.1.trans (hroot.trans hR)
    refine ⟨by dsimp only [NativeLocalTime.steps]; omega,?_⟩
    exact (NativeLocalTime.entry_bound cfg n W hnW).trans (by dsimp only [NativeLocalTime.time]; omega)
  · intro fuel n G _ k cursor hi small
    have hres := uniform n hi.2.1 hi.2.2.1
    have hnW : n ≤ W := hi.2.2.1.trans (hroot.trans hR)
    have hentry := NativeLocalTime.entry_bound cfg n W hnW
    have hsmall := NativeExhaustiveResources.node_time cfg.a cfg.K cfg.b n D k R hres hi.2.2.2.2.1 small
    have hpow := Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left (Nat.add_le_add_right hR 2) 3)
    refine ⟨by dsimp only [NativeLocalTime.steps]; omega,?_⟩
    dsimp only [NativeLocalTime.time]
    omega
  · intro fuel n G _ k front hi small hk
    have hres := uniform n hi.2.1 hi.2.2.1
    have hnR : n ≤ R := hi.2.2.1.trans hroot
    have hnW : n ≤ W := hnR.trans hR
    have hrR : NativeSelectedRounds.level cfg n D ≤ R := by
      dsimp only [ParameterResources.resource,NativeSelectedRounds.level] at hres ⊢; omega
    have hNR : N cfg n D ≤ R := by
      dsimp only [ParameterResources.resource,N,NativeSelectedRounds.level] at hres ⊢; omega
    have hlR : load cfg.b n D ≤ R := by dsimp only [ParameterResources.resource] at hres; omega
    have hiR : limit cfg n D ≤ R := by dsimp only [ParameterResources.resource,limit] at hres ⊢; omega
    have hstack : front.length+frameLength cfg W ≤ capacity cfg rootN W := by
      have h := hi.2.2.2.2.2.2
      have hm : frameLength cfg W ≤ (fuel+1)*frameLength cfg W := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hbounds := NativeRootWorkspace.bounds cfg p q c rootN originalN R W w hK hb hroot budget host G
      D k fuel front hi.2.1 (by omega) hk (by have hf := (fuel_bound hi).trans rootDepth; omega) hres hstack
    let childSteps := NativeRecursionBudget.work (NativeLocalTime.steps W) (NativeLocalTime.branches W) fuel
    let childTime := NativeRecursionBudget.work (NativeLocalTime.time cfg W (stride W)) (NativeLocalTime.branches W) fuel
    have rounds := NativeSelectedRounds.rounds hereditary p q cfg hpc hpcoeff hqc hqcoeff encoded hsep correct hK hb G
      D k fuel (stride W) W c R w rootN (capacity cfg rootN W) childSteps childTime
      (extent cfg rootN W originalN) front hi (by omega) hD (by omega) program hbounds
    refine
      { M := 2^(100*(R+1))
        farM := 2^(2*H p R+1)
        nearM := 2^H p R
        costH := 2*H p R
        T := R+1
        space := space cfg p q n D k R
        oracleTime := NativeSelectedLP.oracleTime p R
        callCost := NativeSelectedLP.callCost p R
        flowTime := flowTime cfg p q n D k R
        c := c
        roundH := NativeOraclePrecision.roundedHeight p.width R
        oracleLocal := oracleLocal cfg p q n D k R (stride W)
        roundCost := roundCost cfg p c R
        data := rounds
        steps := ?_
        time := ?_
        branching := ?_ }
    · have hmul := Nat.mul_le_mul (show 5*(n+1)+7 ≤ 5*(W+1)+7 by omega) (hiR.trans hR)
      exact Nat.add_le_add_left hmul 2
    · have horacle := NativeLocalTime.oracle_bound cfg p q n D k R W (stride W) hR hnW (hrR.trans hR) (hNR.trans hR)
        (by change NativeSelectedLP.certificateHeight p R ≤ W; omega) (by omega)
        (NativeSelectedBudget.flow_time cfg p q c R W n D k hnR hlR (hk.trans hnR) budget)
      have hround : roundCost cfg p c R ≤ W := by omega
      have hmul := Nat.mul_le_mul (Nat.add_le_add horacle hround) (hiR.trans hR)
      have hentry := NativeLocalTime.entry_bound cfg n W hnW
      have hlarge := NativeLocalTime.large_bound cfg n (NativeSelectedRounds.level cfg n D) W hnW (hrR.trans hR) (hNR.trans hR)
      change NativeNodeTrace.entryCost cfg.a n+NativeLargeNode.cost cfg.a n (NativeSelectedRounds.level cfg n D)+2+
        (oracleLocal cfg p q n D k R (stride W)+roundCost cfg p c R)*limit cfg n D ≤ NativeLocalTime.time cfg W (stride W)
      dsimp only [NativeLocalTime.time]
      omega
    · exact Nat.mul_le_mul (Nat.add_le_add_right hnW 1) (hiR.trans hR)

end Lax263307Proofs.NativeSelectedExecution
