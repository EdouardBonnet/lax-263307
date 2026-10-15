import Lax263307Proofs.NativeSelectedRounds
import Lax263307Proofs.NativeEntryResources
import Lax263307Proofs.NativePolynomialEnvelope
import Lax263307Proofs.NativeFlowBudget

set_option maxHeartbeats 350000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedBudget

open Lax263307 NativeCoreMachine NativePolynomialEnvelope

/-- The finite list of root demands, before recursion frames and local
control costs. Their latter dependence on workspace is polynomial too. -/
noncomputable def demand {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (c R : ℕ) : ℕ :=
  R+NativeSelectedLP.certificateHeight p R+NativeOraclePrecision.roundedHeight p.width R+NativeProjectionResources.wordHeight R+NativeEntryResources.amount cfg R+NativeNearResources.space R+
  NativeProjectionResources.space R (NativeSelectedLP.oracleTime p R)+NativeSelectedLP.wordHeight p R+
  (NativeCutResources.wordExponent R (2*NativeSelectedLP.certificateHeight p R+1)+4)+
  NativeSelectedLP.queryBound R+NativeSelectedLP.callCost p R+
  (NativeFlowBudget.widthPolynomial cfg.b (NativePolynomialBudget.heightPolynomial p.width) q.width q.time q.output q.code).eval R+
  (NativeFlowBudget.spacePolynomial cfg.b (NativePolynomialBudget.heightPolynomial p.width) q.time).eval R+
  (NativeFlowBudget.timePolynomial cfg.b (NativePolynomialBudget.heightPolynomial p.width) q.time q.code q.coeff).eval R+
  NativeRoundedResources.space c R (NativeOraclePrecision.roundedHeight p.width R)+
  NativeSelectedRounds.roundCost cfg p c R+100

theorem polynomial {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (c : ℕ) : Bounded (demand cfg p q c) := by
  change Bounded (fun R => demand cfg p q c R)
  simp only [demand,
    NativeEntryResources.amount,
    NativeNearResources.space,
    NativeProjectionResources.space,
    NativeSelectedLP.wordHeight,
    NativeSelectedLP.certificateHeight,
    NativeSelectedLP.invocationHeight,
    NativeSelectedLP.oracleTime,
    NativeSelectedLP.callCost,
    NativeSelectedLP.queryBound,
    NativeSelectedRounds.roundCost,
    NativeCutResources.wordExponent,
    NativeRoundedResources.space,
    NativeOraclePrecision.roundedHeight,
    NativeOraclePrecision.certificateHeight,
    NativeDistanceOracle.cost,
    NativeDistanceInput.cost,
    NativeProjectionResult.cost,
    NativeRoundedUpdate.timeBound,
    NativeRawOracle.cost,
    NativeProjectionResources.wordHeight,
    NativeProjectionResources.shape,
    NativeDistanceData.shapeSize,
    NativeDistanceData.wordLength,
    NativeDistanceData.rows,
    NativeDistanceData.columns,
    NativeProjectionQueryBounds.queryBound,
    NativeDistanceQueryResources.sizeBound,
    NativeProjectionQueryBounds.rootRows,
    NativeProjectionQueryBounds.rootHeight,
    NativeProjectionQueryBounds.scaleHeight,
    NativeQuadraticResources.square_power,
    Nat.size_pow]
  polynomial_envelope

theorem exists_budget {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (c : ℕ) :
    ∃ Q e : ℕ,0<Q ∧ 0<e ∧ ∀ R,demand cfg p q c R≤Q*(R+1)^e :=
  monomial (polynomial cfg p q c)

theorem cost_height {lp : List ℕ → List ℕ} (p : NativeSelectedLP.Program lp) (R : ℕ) :
    2*NativeSelectedLP.certificateHeight p R ≤ (NativePolynomialBudget.heightPolynomial p.width).eval R := by
  have h := NativePolynomialBudget.height_bound p.width R
  have hm : 2*NativeSelectedLP.certificateHeight p R+1 ≤
      (R+1)*(2*NativeSelectedLP.certificateHeight p R+1) := Nat.le_mul_of_pos_left _ (by omega)
  dsimp only [NativeOraclePrecision.roundedHeight] at h
  change 80*(R+1)+(R+1)*(2*NativeSelectedLP.certificateHeight p R+1)+2*R+1 ≤ _ at h
  omega

theorem flow_time {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (c R W n D k : ℕ)
    (hn : n ≤ R) (hl : AlgorithmParameters.load cfg.b n D ≤ R) (hk : k ≤ R)
    (hw : demand cfg p q c R ≤ W) : NativeSelectedRounds.flowTime cfg p q n D k R ≤ W := by
  have h := NativeFlowBudget.time_bound cfg.b n (NativeSelectedRounds.flowH cfg p n D k R) R
    (NativePolynomialBudget.heightPolynomial p.width) q.time q.code q.coeff hn
    (NativeFlowBudget.height_bound cfg.b n (AlgorithmParameters.load cfg.b n D) k
      (2*NativeSelectedLP.certificateHeight p R) R (NativePolynomialBudget.heightPolynomial p.width)
      hn hl hk (cost_height p R))
  dsimp only [demand] at hw
  exact h.trans (by omega)

end Lax263307Proofs.NativeSelectedBudget
