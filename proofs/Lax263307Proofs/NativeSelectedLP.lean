import Lax263307Proofs.NativeProjectionResources
import Lax263307Proofs.NativeOraclePrecision

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedLP

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 DistanceProjection NativeDistanceData

/-- Retain the width guarantee for the same LP program that is invoked
by the native command. No separately chosen output-width polynomial is used. -/
structure Program (f : List ℕ → List ℕ) where
  code : Lax808846.Ram.Program
  width : Polynomial ℕ
  time : Polynomial ℕ
  coeff : List ℕ
  coefficients : ∀ z : ℕ,RamPolynomial.value coeff z=width.eval z
  fits : ∀ (m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n) (x : Fin n → ℚ),
    FitsInWords (width.eval (bitSize (encodeProgram (distanceProgram P x))))
      (f (encodeProgram (distanceProgram P x)))
  call : ∀ (m n : ℕ) (P : Lax109476.LinearProgram.Program ℚ m n) (x : Fin n → ℚ) (ρ : ℚ) (M B : ℕ),
    let query := encodeProgram (distanceProgram P x)
    shapeSize m n<B → Bounded B P x → 2^(width.eval (bitSize query))≤M →
    NativeSignedArithmetic.Bounded M ρ → 2*M^2+3<B → bitSize query+1<B →
    width.eval (bitSize query+1)<B → time.eval (bitSize query)+1<B →
    RamVirtualConstants.allowance code<B →
    Spec B (fun σ => NativeProjectionTrace.InvocationInput P x ρ (time.eval (bitSize query)) σ)
      (NativeProjectionOracle.command code coeff)
      (fun _ τ => NativeProjectionResult.Output
        (RationalProjection.classify P ρ (RegisteredLP.certificate f (distanceProgram P x))) τ ∧
        Prefix (encodeProgram P) "lp.input" τ ∧ Prefix (encodeVector x) "projection.center" τ ∧
        τ.vars "projection.n"=n)
      (NativeDistanceOracle.cost m n code coeff (time.eval (bitSize query)) (bitSize query)+25+
        NativeProjectionResult.cost M n)

theorem exists_program (f : List ℕ → List ℕ) (hf : RamPolytime f) (he : NativeEncodedLP.Encoded f) :
    Nonempty (Program f) := by
  obtain ⟨p,wp,tp,coeff,hcoeff,hfits,hcall⟩ := NativeProjectionOracle.exists_invocation f hf he
  exact ⟨⟨p,wp,tp,coeff,hcoeff,hfits,hcall⟩⟩

def queryBound (R : ℕ) : ℕ := NativeProjectionQueryBounds.queryBound R
def certificateHeight {f : List ℕ → List ℕ} (p : Program f) (R : ℕ) : ℕ := p.width.eval (queryBound R)
def invocationHeight {f : List ℕ → List ℕ} (p : Program f) (R : ℕ) : ℕ :=
  certificateHeight p R+1000*(R+1)^5+1
def oracleTime {f : List ℕ → List ℕ} (p : Program f) (R : ℕ) : ℕ := p.time.eval (queryBound R)
def callCost {f : List ℕ → List ℕ} (p : Program f) (R : ℕ) : ℕ :=
  NativeDistanceOracle.cost (NativeProjectionQueryBounds.rootRows R) R p.code p.coeff
    (oracleTime p R) (queryBound R)+25+NativeProjectionResult.cost (2^invocationHeight p R) R
def wordHeight {f : List ℕ → List ℕ} (p : Program f) (R : ℕ) : ℕ :=
  2*invocationHeight p R+NativeProjectionQueryBounds.rootHeight R+
    NativeProjectionResources.shape R+queryBound R+p.width.eval (queryBound R+1)+
    oracleTime p R+RamVirtualConstants.allowance p.code+100

theorem certificate_bound {f : List ℕ → List ℕ} (p : Program f) (he : NativeEncodedLP.Encoded f)
    {m n : ℕ} (P : Lax109476.LinearProgram.Program ℚ m n) (x : Fin n → ℚ) (R : ℕ)
    (hq : bitSize (encodeProgram (distanceProgram P x))≤queryBound R) :
    NativeProjectionResult.CertificateBounded (2^certificateHeight p R)
      (RegisteredLP.certificate f (distanceProgram P x)) := by
  apply NativeProjectionOracle.certificate_bound
  intro z hz
  have hz' : z∈f (encodeProgram (distanceProgram P x)) := by rwa [(he _ _ _).1]
  exact (p.fits _ _ P x z hz').le.trans
    (Nat.pow_le_pow_right (by decide) (NativeFlowQueryResources.eval_mono p.width hq))

theorem distance_cost_mono (m n M N T U s t : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ)
    (hm : m≤M) (hn : n≤N) (hT : T≤U) (hs : s≤t) :
    NativeDistanceOracle.cost m n p coeff T s≤NativeDistanceOracle.cost M N p coeff U t := by
  dsimp only [NativeDistanceOracle.cost,NativeDistanceInput.cost,NativeDistanceData.wordLength,
    NativeDistanceData.rows,NativeDistanceData.columns]
  gcongr

/-- Invoke the selected LP program under uniform root bounds on storage,
word height and time. Its result is the exact functional projection. -/
theorem invocation {f : List ℕ → List ℕ} (p : Program f)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r D F R w : ℕ)
    (center : MomentLP.Index n r → ℚ) (hn : 0<n) (hD : 0<D) (hF : 0<F)
    (hnR : n≤R) (hkR : k≤R) (hrR : r≤R) (hDR : D≤R) (hFR : F≤R)
    (hNR : MomentLP.dimension n r≤R)
    (hc : ∀ i,NativeRoundedStep.height (center i) (80*(R+1)))
    (hw : wordHeight p R≤w) :
    Spec (2^w) (NativeProjectionTrace.InvocationInput (MomentLP.program G k r)
      (ProjectedOracle.raw center) (NativeNodeTolerance.tolerance n D F) (oracleTime p R))
      (NativeProjectionOracle.command p.code p.coeff)
      (fun _ τ => NativeProjectionResult.Output (NativeOracleExecution.projection f G k D F center) τ ∧
        τ.vars "projection.n"=MomentLP.dimension n r) (callCost p R) := by
  let P := MomentLP.program G k r
  let x := ProjectedOracle.raw center
  let query := encodeProgram (distanceProgram P x)
  let N := MomentLP.dimension n r
  let m := NativeMomentAssembly.rowCount n r
  have hq : bitSize query≤queryBound R :=
    NativeProjectionQueryBounds.uniform_query_size G k r R hnR hkR hrR hNR center hc
  have hm := NativeProjectionResources.rows_bound n r R hnR hNR
  have hshape : shapeSize m N≤NativeProjectionResources.shape R := by
    have h : shapeSize m N≤shapeSize (NativeProjectionQueryBounds.rootRows R) R := by
      dsimp only [shapeSize,NativeDistanceData.wordLength,NativeDistanceData.rows,NativeDistanceData.columns]
      gcongr
    exact h.trans (by dsimp only [NativeProjectionResources.shape]; omega)
  have hsrc : NativeProjectionQueryBounds.height n k r R≤NativeProjectionQueryBounds.rootHeight R := by
    have hp : NativeMomentEncodingHeight.height n k r≤100*(4*R+2)^3+10 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      change n+k+r+MomentLP.dimension n r+2≤4*R+2
      omega
    dsimp only [NativeProjectionQueryBounds.height,NativeProjectionQueryBounds.rootHeight,
      NativeProjectionQueryBounds.scaleHeight]
    omega
  have hbase : 2*invocationHeight p R+NativeProjectionQueryBounds.rootHeight R+
      NativeProjectionResources.shape R+queryBound R+p.width.eval (queryBound R+1)+
      oracleTime p R+RamVirtualConstants.allowance p.code+100≤w := hw
  have hB : w<2^w := Nat.lt_two_pow_self
  have hsourceWord : 2^NativeProjectionQueryBounds.height n k r R≤2^w :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have small := NativeProjectionQueryBounds.bounded G k r R center hc
  have bounded : Bounded (2^w) P x :=
    ⟨small.one.trans_le hsourceWord,
      fun i j => ⟨(small.matrix i j).1.trans_le hsourceWord,(small.matrix i j).2.trans_le hsourceWord⟩,
      fun i => ⟨(small.bound i).1.trans_le hsourceWord,(small.bound i).2.trans_le hsourceWord⟩,
      fun i => ⟨(small.center i).1.trans_le hsourceWord,(small.center i).2.trans_le hsourceWord⟩⟩
  have hM : 2^p.width.eval (bitSize query)≤2^invocationHeight p R :=
    Nat.pow_le_pow_right (by decide) ((NativeFlowQueryResources.eval_mono p.width hq).trans
      (by dsimp only [invocationHeight,certificateHeight]; omega))
  have htol : NativeSignedArithmetic.Bounded (2^invocationHeight p R) (NativeNodeTolerance.tolerance n D F) := by
    have hd := NativeNodeTolerance.coordinates n D F hn hD hF
    have ht := NativeProjectionResources.tolerance_guard n D F R hnR hDR hFR
    have ht' : NativeNodeTolerance.denominator n D F≤1000*(R+1)^5 := by
      dsimp only [NativeNodeTolerance.guard] at ht; omega
    rw [NativeSignedArithmetic.Bounded,hd.1,hd.2,Int.natAbs_one]
    exact ⟨Nat.one_le_two_pow,ht'.trans ((show 1000*(R+1)^5 ≤ invocationHeight p R by
      dsimp only [invocationHeight]; omega).trans Nat.lt_two_pow_self.le)⟩
  have hhost : 2*(2^invocationHeight p R)^2+3<2^w := by
    have hexp : 2*invocationHeight p R+4≤w := by omega
    have hp := Nat.pow_le_pow_right (by decide : 1≤2) hexp
    have he : 2^(2*invocationHeight p R+4)=16*(2^invocationHeight p R)^2 := by
      rw [pow_add,Nat.mul_comm 2 (invocationHeight p R),pow_mul]; norm_num; ring
    rw [he] at hp
    have hpos := Nat.one_le_pow (invocationHeight p R) 2 (by decide)
    nlinarith only [hp,hpos]
  have hwp := NativeFlowQueryResources.eval_mono p.width (Nat.add_le_add_right hq 1)
  have htp : p.time.eval (bitSize query)≤oracleTime p R := NativeFlowQueryResources.eval_mono p.time hq
  have call := p.call m N P x (NativeNodeTolerance.tolerance n D F) (2^invocationHeight p R) (2^w)
    (hshape.trans_lt ((by omega : NativeProjectionResources.shape R≤w).trans_lt hB))
    bounded hM htol hhost ((by omega : bitSize query+1≤w).trans_lt hB)
    (hwp.trans_lt ((by omega : p.width.eval (queryBound R+1)≤w).trans_lt hB))
    ((by omega : p.time.eval (bitSize query)+1≤w).trans_lt hB)
    ((by omega : RamVirtualConstants.allowance p.code≤w).trans_lt hB)
  intro σ hi
  obtain ⟨τ,rr,po⟩ := call σ ⟨hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.1,
    htp.trans_lt hi.2.2.2.2.2.1,htp.trans_lt hi.2.2.2.2.2.2.1,htp.trans_lt hi.2.2.2.2.2.2.2⟩
  refine ⟨τ,rr.mono ?_,po.1,po.2.2.2⟩
  have hcost := distance_cost_mono m N (NativeProjectionQueryBounds.rootRows R) R
    (p.time.eval (bitSize query)) (oracleTime p R) (bitSize query) (queryBound R) p.code p.coeff hm hNR htp hq
  have hreply : NativeProjectionResult.cost (2^invocationHeight p R) N≤
      NativeProjectionResult.cost (2^invocationHeight p R) R := by
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hNR 1)) 200
  exact Nat.add_le_add (Nat.add_le_add_right hcost 25) hreply

end Lax263307Proofs.NativeSelectedLP
