import Lax263307Proofs.NativeSelectedOracle
import Lax263307Proofs.NativeOracleCutHeight
import Lax263307Proofs.NativeRoundedResources

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedRounds

open Lax263307 GraphClasses AlgorithmParameters RoundedOracleSearch Matrix
open NativeCoreMachine

abbrev level (cfg : Config) (n D : ℕ) := AlgorithmParameters.level cfg.a cfg.K cfg.b n D
abbrev F (cfg : Config) (n D : ℕ) := (floorDenominator cfg.a cfg.K cfg.b n D)^(level cfg n D)
abbrev N (cfg : Config) (n D : ℕ) := MomentLP.dimension n (level cfg n D)
abbrev limit (cfg : Config) (n D : ℕ) := iterations cfg.a cfg.K cfg.b n D
abbrev H {lp : List ℕ → List ℕ} (p : NativeSelectedLP.Program lp) (R : ℕ) := NativeSelectedLP.certificateHeight p R
abbrev flowH {lp : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp) (n D k R : ℕ) :=
  NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H p R)
abbrev space {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (n D k R : ℕ) := NativeUniformFlow.spaceBound n (flowH cfg p n D k R) q.time
abbrev flowTime {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (n D k R : ℕ) :=
  NativeSeparatorOutput.timeBound n (flowH cfg p n D k R) q.code q.coeff q.time

def oracleLocal {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (n D k R S : ℕ) : ℕ :=
  (16*NativeMomentInput.length n (level cfg n D)+(36*(2^(100*(R+1))).size+124)*N cfg n D+135+
    NativeSelectedLP.callCost p R+2)+14+(193*N cfg n D+48)+
    NativeNearExecution.timeBound cfg n (level cfg n D) (2^H p R) S (2*H p R) 0 (flowTime cfg p q n D k R)+6

def roundCost {lp : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp) (c R : ℕ) : ℕ :=
  NativeRoundedUpdate.timeBound cfg.rounded c R (NativeOraclePrecision.roundedHeight p.width R) R+16

/-- Only arithmetic and storage inequalities remain in this interface.
All oracle, rounded-program and recursive callback execution is constructed. -/
structure Bounds {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k fuel S v c R w : ℕ) (extent : String → ℕ) (front : List ℕ) : Prop where
  nR : n≤R
  kR : k≤R
  levelR : level cfg n D≤R
  denominatorR : D≤R
  floorR : F cfg n D≤R
  dimensionR : N cfg n D≤R
  roundsR : limit cfg n D≤R
  projection : NativeOracleExecution.ProjectionBounds D k (level cfg n D) (F cfg n D)
    (2^(100*(R+1))) w (NativeSelectedLP.oracleTime p R) G extent
  near : NativeNearExecution.Bounds n (level cfg n D) D k (sparsity cfg.a cfg.K cfg.b n D)
    (2^H p R) (2*H p R) (R+1) fuel S w cfg extent front
  lpWidth : NativeSelectedLP.wordHeight p R≤w
  farWidth : NativeCutResources.wordExponent (N cfg n D) (2*H p R+1)+4≤w
  queryRoom : NativeSelectedLP.queryBound R<extent "vm.input"
  flowWidth : NativeUniformFlow.wordHeight n (flowH cfg p n D k R) q.code q.width q.time q.output≤w
  flowSpace : ∀ a∈NativeSeparatorContext.workspace,space cfg p q n D k R≤extent a
  roundedWidth : c*(2*R+NativeOraclePrecision.roundedHeight p.width R+1)^12≤v
  roundedHost : NativeRoundedResources.wordHeight cfg.rounded v R (NativeOraclePrecision.roundedHeight p.width R)≤w
  roundedSpace : ∀ a∈NativeRoundedResources.buffers,
    NativeRoundedResources.space c R (NativeOraclePrecision.roundedHeight p.width R)≤extent a

theorem rounded_cost_mono (p : Lax808846.Ram.Program) (c n N h j J : ℕ) (hn : n≤N) (hj : j≤J) :
    NativeRoundedUpdate.timeBound p c n h j≤NativeRoundedUpdate.timeBound p c N h J := by
  dsimp only [NativeRoundedUpdate.timeBound,NativeRawOracle.cost]
  gcongr

theorem near_time_affine (cfg : Config) (n r M S h childTime flowTime : ℕ) :
    NativeNearExecution.timeBound cfg n r M S h childTime flowTime=
      NativeNearExecution.timeBound cfg n r M S h 0 flowTime+(n+1)*childTime := by
  dsimp only [NativeNearExecution.timeBound,NativeCollectionExecution.partCost]
  ring

theorem rounds {C : GraphClass} (hereditary : IsHereditary C)
    {lp flow : List ℕ → List ℕ} (p : NativeSelectedLP.Program lp) (q : NativeSelectedNear.Program flow)
    (cfg : Config) (hpc : p.code=cfg.lp) (hpcoeff : p.coeff=cfg.lpWidth)
    (hqc : q.code=cfg.flow) (hqcoeff : q.coeff=cfg.flowWidth)
    (encoded : NativeEncodedLP.Encoded lp) (hsep : NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b)
    (correct : NativeRecursiveOracle.OracleCorrect C lp flow cfg.a cfg.K cfg.b) (hK : 0<cfg.K) (hb : 0<cfg.b)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k fuel S v c R w rootN capacity childSteps childTime : ℕ)
    (extent : String → ℕ) (front : List ℕ)
    (hi : NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length)
      capacity (fuel+1) n G k front.length)
    (hn : 1<n) (hD : 4≤D) (hlarge : cutoff cfg.a cfg.K cfg.b n D<k)
    (program : NativeOracleRounds.Program cfg.rounded c)
    (bounds : Bounds cfg p q G D k fuel S v c R w extent front) :
    NativeRecursiveSetup.Rounds (r:=level cfg n D) D k (sparsity cfg.a cfg.K cfg.b n D) cfg.b (load cfg.b n D)
      (F cfg n D) fuel S v (limit cfg n D) w (2^(100*(R+1))) (2^(2*H p R+1)) (2^H p R) (2*H p R)
      (R+1) (space cfg p q n D k R) (NativeSelectedLP.oracleTime p R) (NativeSelectedLP.callCost p R)
      (flowTime cfg p q n D k R) childSteps childTime c (NativeOraclePrecision.roundedHeight p.width R)
      (oracleLocal cfg p q n D k R S+(n+1)*childTime) (roundCost cfg p c R)
      cfg G lp flow extent front (NativeNodeExecution.child cfg lp flow D fuel G)
      (NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length) capacity) := by
  let oracle := NativeOracleRounds.oracle (r:=level cfg n D) lp flow G D k
    (sparsity cfg.a cfg.K cfg.b n D) cfg.b (load cfg.b n D) (F cfg n D)
    (NativeNodeExecution.child cfg lp flow D fuel G)
  have heq : oracle=fun (_ : ℕ) center => ProjectedOracle.run lp flow cfg.a cfg.K cfg.b D G k
      (NativeRecursiveOracle.child lp flow cfg.a cfg.K cfg.b D fuel G) center := by
    funext j center
    exact NativeOracleExecution.actual_reply lp flow cfg.a cfg.K cfg.b D k fuel G center
  have hdepth : RecursionDepth.depth n≤fuel+1 := hi.2.2.2.2.2.1
  have hdim : 2≤N cfg n D := CoordinateCatalog.catalog_two n (level cfg n D) (by omega)
  have hfloor : 0<F cfg n D := by
    apply Nat.pow_pos
    unfold floorDenominator sparsity targetThreshold load logarithm
    positivity
  have trajectory (j : ℕ) (hj : j<limit cfg n D) :
      (∀ i l,NativeRoundedStep.height ((trajectory oracle j).1 i l) (80*(R+1))) ∧
      (∀ i,NativeRoundedStep.height ((trajectory oracle j).2 i) (80*(R+1))) ∧
      ∀ normal,oracle j (trajectory oracle j).2=.cut normal →
        0<dotProduct (rationalNormal normal) ((trajectory oracle j).1 *ᵥ rationalNormal normal) := by
    have h := NativeRecursiveOracle.trajectory_guards hereditary correct G hi.1 hn D k fuel R j hD hlarge hdepth
      bounds.dimensionR (by have hh := bounds.roundsR; omega)
    simpa only [heq] using h
  refine ⟨program,?_,?_,?_,?_⟩
  · intro j hj
    exact NativeSelectedOracle.setup hereditary p q cfg hpc hpcoeff hqc hqcoeff encoded hsep hK hb G
      D k fuel S v R (F cfg n D) w rootN capacity childSteps childTime extent front hi hn hD hfloor hlarge
      bounds.nR bounds.kR bounds.levelR bounds.denominatorR bounds.floorR bounds.dimensionR
      (RoundedOracleSearch.trajectory oracle j) (trajectory j hj).2.1 bounds.projection bounds.near
      bounds.lpWidth bounds.farWidth bounds.queryRoom bounds.flowWidth bounds.flowSpace _
  · intro j hj normal hnormal
    have heights := trajectory j hj
    have hnormalHeight := NativeOracleCutHeight.normal_height hsep hK hb encoded p G hi.1 D k R (F cfg n D) j
      (by omega) hD hlarge bounds.nR bounds.kR bounds.levelR bounds.dimensionR
      (RoundedOracleSearch.trajectory oracle j).2 heights.2.1 _ normal hnormal
    have hroundH : 1≤NativeOraclePrecision.roundedHeight p.width R := by
      dsimp only [NativeOraclePrecision.roundedHeight]; omega
    have hheight : 80*(R+1)≤NativeOraclePrecision.roundedHeight p.width R := by
      dsimp only [NativeOraclePrecision.roundedHeight]; omega
    exact NativeRoundedResources.bounds cfg.rounded c _ v n j (limit cfg n D) R w extent
      (RoundedOracleSearch.trajectory oracle j) normal hdim hroundH bounds.dimensionR bounds.nR
      (by have hh := bounds.roundsR; omega) bounds.roundsR
      (fun i l => NativeOraclePrecision.height_mono _ _ _ (heights.1 i l) hheight) hnormalHeight
      (fun i => NativeOraclePrecision.height_mono _ _ _ (heights.2.1 i) hheight)
      (heights.2.2 normal hnormal) bounds.roundedWidth bounds.roundedHost bounds.roundedSpace
  · rw [NativeMomentInput.input_length,near_time_affine]
    dsimp only [oracleLocal,N]
    omega
  · intro j hj
    exact Nat.add_le_add_right (rounded_cost_mono cfg.rounded c (N cfg n D) R _ j R bounds.dimensionR
      (by have hh := bounds.roundsR; omega)) 16

end Lax263307Proofs.NativeSelectedRounds
