import Lax263307Proofs.NativeSplitInput
import Lax263307Proofs.NativeOracleScalars

namespace Lax263307Proofs.NativeSplitOracle

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

def query {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) : List ℕ :=
  Lax455465.RationalEncoding.encodeInput .directed (splitInstance (restriction G R) (fun v => x (label R v)) large)

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq NativeSplitInput.command (NativeOracleCalls.command p coeff)

def cost (r : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ) (T size : ℕ) : ℕ :=
  488*r*r+56*r+36+
    (((12*size+39)*NativeSplitInput.wordLength r+6*coeff.length+29)+
      ((T+1)*(4*p.length+32*T+104)+18))

theorem data_frame {B K n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → ℚ≥0} {R : Finset (Fin n)} {large : ℚ≥0}
    {p : Lax808846.Ram.Program} {coeff : List ℕ} {σ τ : Env}
    (rr : Run B (NativeOracleCalls.command p coeff) σ τ K) (hd : NativeSplitEntry.Data G x R large σ) :
    NativeSplitEntry.Data G x R large τ := by
  apply NativeSplitEntry.frame rr hd
  · intro s hs
    apply NativeOracleFrame.command_array p coeff s
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl <;> decide
  · intro s hs
    apply NativeOracleScalars.command_variable p coeff s
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Build the split query and execute the same fixed flow function
selected by the functional correctness theorem. The original graph,
costs, and induced vertex labels survive the call. -/
theorem exists_invocation (f : List ℕ → List ℕ) (hf : RamPolytime f) :
    ∃ (p : Lax808846.Ram.Program) (wp tp : Polynomial ℕ) (coeff : List ℕ),
    (∀ z : ℕ,RamPolynomial.value coeff z=wp.eval z) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
      (R : Finset (Fin n)) (large : ℚ≥0),
    let q := query G x R large
    FitsInWords (wp.eval (bitSize q)) ((q.length::q)++f q) ∧
    ∀ B M : ℕ,1≤M → 8*n*n+6*n+M+40<B → (∀ v,Bounded M (x v : ℚ)) → Bounded M (large : ℚ) →
      bitSize q+1<B → wp.eval (bitSize q+1)<B → 2*(2^wp.eval (bitSize q))^2+3<B →
      tp.eval (bitSize q)+1<B → RamVirtualConstants.allowance p<B →
      Spec B (fun σ => NativeRestrictionRead.Data G (fun v => (x v : ℚ)) R σ ∧
        Stored "split.large" (large : ℚ) σ ∧ NativeSplitInput.wordLength R.card<(σ.arrs "lp.word").length ∧
        q.length<(σ.arrs "vm.input").length ∧ tp.eval (bitSize q)<(σ.arrs "vm.addresses").length ∧
        tp.eval (bitSize q)<(σ.arrs "vm.values").length ∧ tp.eval (bitSize q)<(σ.arrs "vm.output").length)
        (command p coeff) (fun _ τ => NativeSplitEntry.Data G x R large τ ∧ Prefix (f q) "vm.output" τ ∧
          τ.vars "vm.outputLength"=(f q).length ∧ τ.vars "vm.running"=0)
        (cost R.card p coeff (tp.eval (bitSize q)) (bitSize q)) := by
  obtain ⟨p,wp,tp,coeff,hcoeff,hcall⟩ := NativeOracleCalls.exists_invocation f hf
  refine ⟨p,wp,tp,coeff,hcoeff,?_⟩
  intro n G _ x R large
  let q := query G x R large
  obtain ⟨hfit,hcall⟩ := hcall q
  refine ⟨hfit,?_⟩
  intro B M hM hshape hx hl hsize hpoly hB htime hallow
  rintro σ ⟨hd,hlσ,hroom,hI,hA,hV,hO⟩
  obtain ⟨ν,r1,p1⟩ := NativeSplitInput.command_spec B M n G x R large hM hshape hx hl σ ⟨hd,hlσ,hroom⟩
  obtain ⟨τ,r2,p2⟩ := hcall B hsize hpoly hB htime hallow ν
    ⟨p1.2.1,by simpa only [q,query,NativeSplitInput.input_length] using p1.2.2,
      by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1],
      by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1]⟩
  exact ⟨τ,(r1.seq r2).mono (by simp only [cost,q,query,NativeSplitInput.input_length]; omega),data_frame r2 p1.1,p2⟩

end Lax263307Proofs.NativeSplitOracle
