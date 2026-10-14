import Lax263307Proofs.NativeDistanceOracle
import Lax263307Proofs.NativeProjectionResult
import Lax263307Proofs.NativeProjectionTolerance
import Lax263307Proofs.NativeEncodedLP

set_option maxRecDepth 10000
set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeProjectionOracle

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307.DistanceProjection Lax263307.RationalProjection
open NativeDistanceData

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq (NativeDistanceOracle.command p coeff)
    (.seq NativeProjectionTolerance.command NativeProjectionResult.command)

theorem certificate_bound (M m n : ℕ) (c : Certificate (m+(n+n)) (n+1))
    (hc : ∀ v∈encodeCertificate c,v≤M) : NativeProjectionResult.CertificateBounded M c := by
  cases c with
  | optimal z y =>
    constructor
    · intro i
      apply NativeEncodedLP.coordinate_bounds M (n+1) z _ i
      intro v hv
      exact hc v (List.mem_append_left _ (List.mem_append_right _ hv))
    · intro i
      apply NativeEncodedLP.coordinate_bounds M (m+(n+n)) y _ i
      intro v hv
      exact hc v (List.mem_append_right _ hv)
  | infeasible _ => trivial
  | unbounded _ _ => trivial

theorem tolerance_frame (p : Lax808846.Ram.Program) (coeff : List ℕ) :
    "projection.tolerance" ∉ (NativeDistanceOracle.command p coeff).warrs := by
  simp only [NativeDistanceOracle.command,Com.warrs,List.mem_append,not_or]
  exact ⟨by decide,NativeOracleFrame.command_array p coeff "projection.tolerance" (by decide)⟩

/-- The full native projection call constructs the distance LP, runs the
specific registered solver, and processes that exact certificate. The
result matches the functional projection branch on every bounded input. -/
theorem exists_invocation (f : List ℕ → List ℕ) (hf : RamPolytime f) (he : NativeEncodedLP.Encoded f) :
    ∃ (p : Lax808846.Ram.Program) (wp tp : Polynomial ℕ) (coeff : List ℕ),
    (∀ z : ℕ,RamPolynomial.value coeff z=wp.eval z) ∧
    (∀ (m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ),
      FitsInWords (wp.eval (bitSize (encodeProgram (distanceProgram P x))))
        (f (encodeProgram (distanceProgram P x)))) ∧
    ∀ (m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (ρ : ℚ) (M B : ℕ),
    let query := encodeProgram (distanceProgram P x)
    shapeSize m n<B → Bounded B P x →
      2^(wp.eval (bitSize query))≤M → NativeSignedArithmetic.Bounded M ρ →
      2*M^2+3<B → bitSize query+1<B → wp.eval (bitSize query+1)<B →
      tp.eval (bitSize query)+1<B → RamVirtualConstants.allowance p<B →
      Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧
        Prefix (encodeVector x) "projection.center" σ ∧
        Prefix (encodeRational ρ) "projection.tolerance" σ ∧
        wordLength m n<(σ.arrs "lp.word").length ∧
        query.length<(σ.arrs "vm.input").length ∧
        tp.eval (bitSize query)<(σ.arrs "vm.addresses").length ∧
        tp.eval (bitSize query)<(σ.arrs "vm.values").length ∧
        tp.eval (bitSize query)<(σ.arrs "vm.output").length)
        (command p coeff)
        (fun _ τ => NativeProjectionResult.Output
            (classify P ρ (Lax263307.RegisteredLP.certificate f (distanceProgram P x))) τ ∧
          Prefix (encodeProgram P) "lp.input" τ ∧ Prefix (encodeVector x) "projection.center" τ ∧
          τ.vars "projection.n"=n)
        (NativeDistanceOracle.cost m n p coeff (tp.eval (bitSize query)) (bitSize query)+25+
          NativeProjectionResult.cost M n) := by
  obtain ⟨p,wp,tp,coeff,hcoeff,hcall⟩ := NativeDistanceOracle.exists_invocation f hf
  refine ⟨p,wp,tp,coeff,hcoeff,?_,?_⟩
  · intro m n P x v hv
    exact (hcall m n P x).1 v (List.mem_append_right _ hv)
  intro m n P x ρ M B
  dsimp only
  let query := encodeProgram (distanceProgram P x)
  intro hshape hb hM hρ hB hsize hpoly htime hallow
  obtain ⟨hfit,hcall⟩ := hcall m n P x
  let c := Lax263307.RegisteredLP.certificate f (distanceProgram P x)
  have henc : f query=encodeCertificate c := (he _ _ (distanceProgram P x)).1
  dsimp only [query] at henc
  have hc : NativeProjectionResult.CertificateBounded M c := by
    apply certificate_bound M m n c
    intro v hv
    have hv' : v∈f query := by rwa [henc]
    exact (hfit v (List.mem_append_right _ hv')).le.trans hM
  have hhost : 2*(2^wp.eval (bitSize query))^2+3<B := by
    have hh := Nat.mul_le_mul hM hM
    change (2^wp.eval (bitSize query))*(2^wp.eval (bitSize query))≤M*M at hh
    nlinarith only [hh,hB]
  have hMhost : M<B := by nlinarith
  have hs : 3*m+10*n+20<B := by
    dsimp [shapeSize,wordLength,rows,columns] at hshape
    nlinarith [Nat.zero_le (m*n),Nat.zero_le (n*n)]
  have hlength : 3*n≤wordLength m n := by dsimp [wordLength,rows,columns]; omega
  rintro σ ⟨hp,hx,hρwords,hr,hI,hA,hV,hO⟩
  obtain ⟨ν,r1,p1⟩ := hcall B hshape hb hsize hpoly hhost htime hallow σ ⟨hp,hx,hr,hI,hA,hV,hO⟩
  have htolerance : Prefix (encodeRational ρ) "projection.tolerance" ν := by
    simpa only [Prefix,r1.frame_arr "projection.tolerance" (tolerance_frame p coeff)] using hρwords
  obtain ⟨μ,r2,p2⟩ := NativeProjectionTolerance.command_spec B ρ (by omega)
    (hρ.1.trans_lt hMhost) (hρ.2.trans_lt hMhost) ν htolerance
  have hsource : Prefix (encodeProgram P) "lp.input" μ := by
    simpa only [Prefix,r2.frame_arr "lp.input" (by decide)] using p1.2.2.2.1
  have hcert : Prefix (encodeCertificate c) "vm.output" μ := by
    simpa only [Prefix,r2.frame_arr "vm.output" (by decide),henc] using p1.1
  have hroom : 3*n<(μ.arrs "lp.word").length := by
    rw [RamFrames.run_array_length (r1.seq r2)]
    exact hlength.trans_lt hr
  obtain ⟨τ,r3,p3⟩ := NativeProjectionResult.command_spec B M m n P c ρ hB hs hc hρ μ ⟨hsource,hcert,p2,hroom⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),p3.1,p3.2.1,?_,p3.2.2⟩
  simpa only [Prefix,(r2.seq r3).frame_arr "projection.center" (by decide)] using p1.2.2.2.2

end Lax263307Proofs.NativeProjectionOracle
