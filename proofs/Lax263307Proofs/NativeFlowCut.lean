import Lax263307Proofs.NativeSplitOracle
import Lax263307Proofs.NativeShoreOrientation
import Lax263307Proofs.NativeOutputLength

namespace Lax263307Proofs.NativeFlowCut

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

def decoded {n : ℕ} (R : Finset (Fin n)) (xs : List ℕ) : Finset (Fin n) × Finset (Fin n) :=
  let s := orient (NativeFlowShores.left R xs) (NativeFlowShores.right R xs)
  (s.1.image (label R),s.2.image (label R))

theorem step_eq {n : ℕ} (f : List ℕ → List ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (b load k : ℕ) (R : Finset (Fin n)) :
    ComputedSeparators.step f G x b load k R=
      decoded R (f (NativeSplitOracle.query G x R (largeCapacity b n R.card load k))) := rfl

def decodeCommand : Com := .seq NativeFlowShores.command NativeShoreOrientation.command

theorem decode_spec (B n : ℕ) (R : Finset (Fin n)) (xs : List ℕ)
    (hB : xs.length+2*n+4<B) (hm : 2^n<B) (hw : ∀ z∈xs,z<B) :
    Spec B (fun σ => NativeFlowShores.Context R xs σ ∧ σ.vars "graph.n"=n ∧ n≤(σ.arrs "subset.bits").length)
      decodeCommand (fun _ τ => τ.vars "cut.left"=NativeMasks.mask (decoded R xs).1 ∧
        τ.vars "cut.right"=NativeMasks.mask (decoded R xs).2) (59*R.card+42*n+42) := by
  rintro σ ⟨hd,hn,hroom⟩
  obtain ⟨ν,r1,p1⟩ := NativeFlowShores.command_spec B n R xs hB hm hw σ hd
  obtain ⟨τ,r2,p2⟩ := NativeShoreOrientation.command_spec B
    ((NativeFlowShores.left R xs).image (label R)) ((NativeFlowShores.right R xs).image (label R))
    (by omega) hm ν
    ⟨(r1.frame_var "graph.n" (by decide)).trans hn,p1.2.1,p1.2.2,by rwa [RamFrames.run_array_length r1]⟩
  have he := NativeShoreMasks.orient_images (label R) (label R).injective
    (NativeFlowShores.left R xs) (NativeFlowShores.right R xs)
  exact ⟨τ,(r1.seq r2).mono (by omega),by simpa only [←he,decoded] using p2⟩

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq (NativeSplitOracle.command p coeff) decodeCommand

/-- One complete flow-cut call, with exact query construction, execution
of the chosen solver, cut decoding, lifting, and shore orientation. -/
theorem exists_invocation (f : List ℕ → List ℕ) (hf : RamPolytime f) :
    ∃ (p : Lax808846.Ram.Program) (wp tp op : Polynomial ℕ) (coeff : List ℕ),
    (∀ z : ℕ,RamPolynomial.value coeff z=wp.eval z) ∧
    (∀ q : List ℕ,(f q).length≤op.eval (bitSize q)) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0)
      (R : Finset (Fin n)) (large : ℚ≥0),
    let q := NativeSplitOracle.query G x R large
    FitsInWords (wp.eval (bitSize q)) ((q.length::q)++f q) ∧
    ∀ B M : ℕ,1≤M → 8*n*n+6*n+M+40<B → (∀ v,Bounded M (x v : ℚ)) → Bounded M (large : ℚ) →
      bitSize q+1<B → wp.eval (bitSize q+1)<B → 2*(2^wp.eval (bitSize q))^2+3<B →
      tp.eval (bitSize q)+1<B → RamVirtualConstants.allowance p<B →
      op.eval (bitSize q)+2*n+4<B → 2^n<B →
      Spec B (fun σ => NativeRestrictionRead.Data G (fun v => (x v : ℚ)) R σ ∧
        Stored "split.large" (large : ℚ) σ ∧ NativeSplitInput.wordLength R.card<(σ.arrs "lp.word").length ∧
        q.length<(σ.arrs "vm.input").length ∧ tp.eval (bitSize q)<(σ.arrs "vm.addresses").length ∧
        tp.eval (bitSize q)<(σ.arrs "vm.values").length ∧ tp.eval (bitSize q)<(σ.arrs "vm.output").length ∧
        n≤(σ.arrs "subset.bits").length)
        (command p coeff) (fun _ τ => NativeSplitEntry.Data G x R large τ ∧
          τ.vars "cut.left"=NativeMasks.mask (decoded R (f q)).1 ∧
          τ.vars "cut.right"=NativeMasks.mask (decoded R (f q)).2)
        (NativeSplitOracle.cost R.card p coeff (tp.eval (bitSize q)) (bitSize q)+59*R.card+42*n+42) := by
  obtain ⟨p,wp,tp,coeff,hcoeff,hcall⟩ := NativeSplitOracle.exists_invocation f hf
  obtain ⟨op,hop⟩ := NativeOutputLength.exists_bound f hf
  refine ⟨p,wp,tp,op,coeff,hcoeff,hop,?_⟩
  intro n G _ x R large
  let q := NativeSplitOracle.query G x R large
  obtain ⟨hfit,hcall⟩ := hcall n G x R large
  refine ⟨hfit,?_⟩
  intro B M hM hshape hx hl hsize hpoly hB htime hallow hout hm
  rintro σ ⟨hd,hlσ,hroom,hI,hA,hV,hO,hbits⟩
  obtain ⟨ν,r1,p1⟩ := hcall B M hM hshape hx hl hsize hpoly hB htime hallow σ
    ⟨hd,hlσ,hroom,hI,hA,hV,hO⟩
  have hword : 2^wp.eval (bitSize q)<B := by nlinarith [Nat.two_pow_pos (wp.eval (bitSize q))]
  have hwords : ∀ z∈f q,z<B := fun z hz => (hfit z (List.mem_append_right _ hz)).trans hword
  obtain ⟨τ,r2,p2⟩ := decode_spec B n R (f q) (by have hh:=hop q; dsimp only [q] at hh ⊢; omega) hm hwords ν
    ⟨⟨p1.1.1.labels,p1.1.1.count,p1.2.1,p1.2.2.1⟩,p1.1.1.order,by rwa [RamFrames.run_array_length r1]⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),NativeSplitEntry.frame r2 p1.1 (by decide) (by decide),p2⟩

end Lax263307Proofs.NativeFlowCut
