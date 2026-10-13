import Lax263307Proofs.NativeDistanceInput
import Lax263307Proofs.NativeOracleFrame

namespace Lax263307Proofs.NativeDistanceOracle

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307.DistanceProjection NativeDistanceData

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq NativeDistanceInput.command (NativeOracleCalls.command p coeff)

def cost (m n : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ)
    (T size : ℕ) : ℕ := NativeDistanceInput.cost m n+
  (((12*size+39)*wordLength m n+6*coeff.length+29)+
    ((T+1)*(4*p.length+32*T+104)+18))

/-- One fixed host command constructs and submits every distance query to
precisely the solver function supplied by the algorithm's correctness proof.
The base LP and current center survive the complete solver invocation. -/
theorem exists_invocation (f : List ℕ → List ℕ) (hf : RamPolytime f) :
    ∃ (p : Lax808846.Ram.Program) (wp tp : Polynomial ℕ) (coeff : List ℕ),
    (∀ z : ℕ, RamPolynomial.value coeff z=wp.eval z) ∧
    ∀ (m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ),
    let query := encodeProgram (distanceProgram P x)
    FitsInWords (wp.eval (bitSize query)) ((query.length::query)++f query) ∧
    ∀ B : ℕ, shapeSize m n<B → Bounded B P x →
      bitSize query+1<B → wp.eval (bitSize query+1)<B →
      2*(2^wp.eval (bitSize query))^2+3<B →
      tp.eval (bitSize query)+1<B → RamVirtualConstants.allowance p<B →
      Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧
        Prefix (encodeVector x) "projection.center" σ ∧
        wordLength m n<(σ.arrs "lp.word").length ∧
        query.length<(σ.arrs "vm.input").length ∧
        tp.eval (bitSize query)<(σ.arrs "vm.addresses").length ∧
        tp.eval (bitSize query)<(σ.arrs "vm.values").length ∧
        tp.eval (bitSize query)<(σ.arrs "vm.output").length)
        (command p coeff)
        (fun _ τ => Prefix (f query) "vm.output" τ ∧
          τ.vars "vm.outputLength"=(f query).length ∧ τ.vars "vm.running"=0 ∧
          Prefix (encodeProgram P) "lp.input" τ ∧
          Prefix (encodeVector x) "projection.center" τ)
        (cost m n p coeff (tp.eval (bitSize query)) (bitSize query)) := by
  obtain ⟨p,wp,tp,coeff,hcoeff,hcall⟩ := NativeOracleCalls.exists_invocation f hf
  refine ⟨p,wp,tp,coeff,hcoeff,?_⟩
  intro m n P x
  let query := encodeProgram (distanceProgram P x)
  obtain ⟨hfit,hcall⟩ := hcall query
  refine ⟨hfit,?_⟩
  intro B hshape hb hsize hpoly hB htime hallow
  rintro σ ⟨hp,hx,hr,hI,hA,hV,hO⟩
  obtain ⟨ν,r1,p1⟩ := NativeDistanceInput.command_spec B m n P x hshape hb σ ⟨hp,hx,hr⟩
  obtain ⟨τ,r2,p2⟩ := hcall B hsize hpoly hB htime hallow ν
    ⟨p1.2.1,by simpa only [query,NativeDistanceInput.input_length] using p1.2.2,
      by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1],
      by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1]⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [cost,query,NativeDistanceInput.input_length]; omega),
    p2.1,p2.2.1,p2.2.2,?_,?_⟩
  · simpa only [Prefix,NativeOracleFrame.frame_array r2 "lp.input" (by decide)] using p1.1.source
  · simpa only [Prefix,NativeOracleFrame.frame_array r2 "projection.center" (by decide)] using p1.1.center

end Lax263307Proofs.NativeDistanceOracle
