import Lax263307Proofs.NativeSelectedLP
import Lax263307Proofs.NativeSelectedNear

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedOracle

open Lax263307 GraphClasses AlgorithmParameters RoundedOracleSearch
open NativeCoreMachine

theorem far_guard {N : ℕ} (H w : ℕ) (a : Fin N → ℚ)
    (ha : ∀ i,NativeSignedArithmetic.Bounded (2^H) (a i))
    (hw : NativeCutResources.wordExponent N H+4≤w) :
    2^H*RationalCutBuffer.denominator a+2^H+RationalCutBuffer.denominator a+3*N+23<2^w := by
  have h := NativeCutResources.guard_bound N H a ha
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hw
  rw [pow_add] at hp
  norm_num at hp
  have hpos := Nat.two_pow_pos (NativeCutResources.wordExponent N H)
  omega

/-- Supply a complete oracle setup from the same selected LP/flow programs
and the actual recursive child domain. All remaining premises are numerical. -/
theorem setup {C : GraphClass} (hereditary : IsHereditary C)
    {lp flow : List ℕ → List ℕ} (lpProgram : NativeSelectedLP.Program lp)
    (flowProgram : NativeSelectedNear.Program flow) (cfg : Config)
    (hlpCode : lpProgram.code=cfg.lp) (hlpCoeff : lpProgram.coeff=cfg.lpWidth)
    (hflowCode : flowProgram.code=cfg.flow) (hflowCoeff : flowProgram.coeff=cfg.flowWidth)
    (encoded : NativeEncodedLP.Encoded lp)
    (hsep : NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b) (hK : 0<cfg.K) (hb : 0<cfg.b)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k fuel S v R F w rootN capacity childSteps childTime : ℕ)
    (extent : String → ℕ) (front : List ℕ)
    (hi : NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length)
      capacity (fuel+1) n G k front.length)
    (hn : 1<n) (hD : 4≤D) (hF : 0<F) (hlarge : cutoff cfg.a cfg.K cfg.b n D<k)
    (hnR : n≤R) (hkR : k≤R) (hrR : level cfg.a cfg.K cfg.b n D≤R)
    (hDR : D≤R) (hFR : F≤R) (hNR : MomentLP.dimension n (level cfg.a cfg.K cfg.b n D)≤R)
    (state : State (MomentLP.dimension n (level cfg.a cfg.K cfg.b n D)))
    (hcenter : ∀ i,NativeRoundedStep.height (state.2 i) (80*(R+1)))
    (projectionBounds : NativeOracleExecution.ProjectionBounds D k (level cfg.a cfg.K cfg.b n D) F
      (2^(100*(R+1))) w (NativeSelectedLP.oracleTime lpProgram R) G extent)
    (nearBounds : NativeNearExecution.Bounds n (level cfg.a cfg.K cfg.b n D) D k
      (sparsity cfg.a cfg.K cfg.b n D) (2^NativeSelectedLP.certificateHeight lpProgram R)
      (2*NativeSelectedLP.certificateHeight lpProgram R) (R+1) fuel S w cfg extent front)
    (hlpWidth : NativeSelectedLP.wordHeight lpProgram R≤w)
    (hfarWidth : NativeCutResources.wordExponent (MomentLP.dimension n (level cfg.a cfg.K cfg.b n D))
      (2*NativeSelectedLP.certificateHeight lpProgram R+1)+4≤w)
    (hqueryRoom : NativeSelectedLP.queryBound R<extent "vm.input")
    (hflowWidth : NativeUniformFlow.wordHeight n
      (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*NativeSelectedLP.certificateHeight lpProgram R))
      flowProgram.code flowProgram.width flowProgram.time flowProgram.output≤w)
    (hspace : ∀ a∈NativeSeparatorContext.workspace,
      NativeUniformFlow.spaceBound n
        (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*NativeSelectedLP.certificateHeight lpProgram R))
        flowProgram.time≤extent a)
    (child : (A : Finset (Fin n)) → ℕ → Option (Finset (Fin A.card))) :
    NativeRecursiveSetup.Oracle D k (sparsity cfg.a cfg.K cfg.b n D) cfg.b (load cfg.b n D) F fuel S v w
      (2^(100*(R+1))) (2^(2*NativeSelectedLP.certificateHeight lpProgram R+1))
      (2^NativeSelectedLP.certificateHeight lpProgram R) (2*NativeSelectedLP.certificateHeight lpProgram R)
      (R+1)
      (NativeUniformFlow.spaceBound n
        (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*NativeSelectedLP.certificateHeight lpProgram R)) flowProgram.time)
      (NativeSelectedLP.oracleTime lpProgram R) (NativeSelectedLP.callCost lpProgram R)
      (NativeSeparatorOutput.timeBound n
        (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*NativeSelectedLP.certificateHeight lpProgram R))
        flowProgram.code flowProgram.coeff flowProgram.time)
      childSteps childTime cfg G lp flow extent front child state
      (NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length) capacity) := by
  have query := NativeProjectionQueryBounds.uniform_query_size G k _ R hnR hkR hrR hNR state.2 hcenter
  have certificate := NativeSelectedLP.certificate_bound lpProgram encoded (MomentLP.program G k _)
    (ProjectedOracle.raw state.2) R query
  refine ⟨projectionBounds,?_,?_,?_,?_,?_⟩
  · intro i
    exact NativeOraclePrecision.height_mono _ _ _ (hcenter i) (by omega)
  · exact (Lax455465Proofs.WordSize.length_le _).trans_lt (query.trans_lt hqueryRoom)
  · simpa only [hlpCode,hlpCoeff] using NativeSelectedLP.invocation lpProgram G k _ D F R w state.2
      (by omega) (by omega) hF hnR hkR hrR hDR hFR hNR hcenter hlpWidth
  · intro a β hfar
    have ha := NativeNormalHeight.far_height _ (MomentLP.program G k _)
      (NativeNodeTolerance.tolerance n D F) _ certificate a β hfar
    have he : 2*(2^NativeSelectedLP.certificateHeight lpProgram R)^2=
        2^(2*NativeSelectedLP.certificateHeight lpProgram R+1) := by
      rw [pow_add,Nat.mul_comm 2 (NativeSelectedLP.certificateHeight lpProgram R),pow_mul]; norm_num; ring
    rw [he] at ha
    exact ⟨ha,far_guard _ w a ha hfarWidth⟩
  · intro x hx
    have feasible := NativeSelectedParts.near_feasible lp encoded G k (ProjectedOracle.raw state.2)
      (NativeNodeTolerance.tolerance n D F) x hx
    have bounded := NativeSelectedParts.near_bound _ (MomentLP.program G k _)
      (NativeNodeTolerance.tolerance n D F) _ certificate x hx
    exact NativeSelectedNear.setup hereditary flowProgram cfg hflowCode hflowCoeff hsep hK hb G
      D k fuel S v (NativeSelectedLP.certificateHeight lpProgram R) (R+1) w rootN capacity childSteps childTime
      extent front hi hn hD hlarge x feasible bounded (by omega) nearBounds hflowWidth hspace child

end Lax263307Proofs.NativeSelectedOracle
