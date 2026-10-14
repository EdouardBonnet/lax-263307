import Lax263307Proofs.NativeSplitVectors

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeSplitInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic NativeSplitEntry
open scoped NNRat

def wordLength (s : ℕ) : ℕ := 2+4*s+8*s*s

def sizes : Com := .seq (.assign "split.order" (.mul (.lit 2) (.var "restrict.count")))
  (.assign "split.count" (.mul (.var "split.order") (.var "split.order")))

theorem sizes_spec (B n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) (hB : 4*n*n+2*n+3<B) :
    Spec B (fun σ => NativeRestrictionRead.Data G (fun v => (x v : ℚ)) R σ ∧ Stored "split.large" (large : ℚ) σ)
      sizes (fun _ τ => Data G x R large τ) 8 := by
  have hR := NativeMaskUnpack.card_bound R
  have hsize : Spec B (fun σ => σ.vars "restrict.count"=R.card) sizes
      (fun _ τ => τ.vars "split.order"=2*R.card ∧ τ.vars "split.count"=(2*R.card)*(2*R.card)) 8 := by
    have hh : (2*R.card)*(2*R.card)<B := by nlinarith only [hB,Nat.mul_le_mul hR hR]
    run_vcg
    all_goals simp_all
    all_goals omega
  rintro σ ⟨hd,hl⟩
  obtain ⟨τ,rr,ht⟩ := hsize σ hd.count
  exact ⟨τ,rr,NativeRestrictionRead.frame rr hd (by decide) (by decide),
    by simpa only [Stored,String.reduceAppend,rr.frame_var "split.large.s" (by decide),
      rr.frame_var "split.large.n" (by decide),rr.frame_var "split.large.d" (by decide)] using hl,ht⟩

def header : Com := .seq (.assign "lp.position" (.lit 0))
  (.seq (RamWordBuffer.append "lp.word" "lp.position" (.lit 1))
    (RamWordBuffer.append "lp.word" "lp.position" (.var "split.order")))

theorem header_spec (B n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) (hB : 2*R.card+3<B) :
    Spec B (fun σ => Data G x R large σ ∧ 2<(σ.arrs "lp.word").length) header
      (fun _ τ => Data G x R large τ ∧ Prefix [1,2*R.card] "lp.word" τ ∧ τ.vars "lp.position"=2) 16 := by
  rintro σ ⟨hd,hr⟩
  let ν := σ.setVar "lp.position" 0
  have r1 : Run B (.assign "lp.position" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  obtain ⟨μ,r2,p2⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position" [] 1 (.lit 1)
    (by omega) (by simp; omega) ν
    ⟨by simp [Prefix],by simp [ν],by change 0<(σ.arrs "lp.word").length; omega,evalB_lit (by omega)⟩
  have ho : μ.vars "split.order"=2*R.card := ((r1.seq r2).frame_var "split.order" (by decide)).trans hd.2.2.1
  obtain ⟨τ,r3,p3⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position" [1] (2*R.card) (.var "split.order")
    (by omega) (by simp; omega) μ
    ⟨by simpa using p2.1,by simpa using p2.2,
      by rw [RamFrames.run_array_length (r1.seq r2)]; simp only [List.length_singleton]; omega,
      by rw [evalB_var_iff]; exact ⟨ho.symm,ho ▸ (by omega : 2*R.card<B)⟩⟩
  have rr := r1.seq (r2.seq r3)
  exact ⟨τ,rr,frame rr hd (by decide) (by decide),by simpa using p3.1,by simpa using p3.2⟩

def command : Com := .seq sizes (.seq header (.seq NativeSplitVectors.weights NativeSplitVectors.matrix))

theorem input_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) :
    (Lax455465.RationalEncoding.encodeInput .directed
      (splitInstance (restriction G R) (fun v => x (label R v)) large)).length=wordLength R.card := by
  rw [NativeSplitVectors.input_eq]
  simp only [List.length_append,List.length_cons,List.length_nil,RamUnsignedBuffer.length_encode,
    List.length_replicate,NativeSplitVectors.entries,List.length_ofFn,wordLength]
  ring

/-- Construct every word of the actual registered directed flow-cut
query, including the unit demands and row-major split capacities. -/
theorem command_spec (B M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) (hM : 1≤M)
    (hB : 8*n*n+6*n+M+40<B) (hx : ∀ v,Bounded M (x v : ℚ)) (hl : Bounded M (large : ℚ)) :
    Spec B (fun σ => NativeRestrictionRead.Data G (fun v => (x v : ℚ)) R σ ∧
      Stored "split.large" (large : ℚ) σ ∧ wordLength R.card<(σ.arrs "lp.word").length)
      command (fun _ τ => Data G x R large τ ∧
        Prefix (Lax455465.RationalEncoding.encodeInput .directed
          (splitInstance (restriction G R) (fun v => x (label R v)) large)) "lp.word" τ ∧
        τ.vars "lp.position"=wordLength R.card) (488*R.card*R.card+56*R.card+36) := by
  have hR := NativeMaskUnpack.card_bound R
  have hRR := Nat.mul_le_mul hR hR
  have hsmall : 4*n*n+6*n+M+20<B := by nlinarith only [hB]
  have hlen : wordLength R.card+3<B := by dsimp [wordLength]; nlinarith only [hB,hR,hRR]
  rintro σ ⟨hd,hlσ,hroom⟩
  obtain ⟨σ1,r1,p1⟩ := sizes_spec B n G x R large (by omega) σ ⟨hd,hlσ⟩
  obtain ⟨σ2,r2,p2⟩ := header_spec B n G x R large (by dsimp [wordLength] at hlen; omega) σ1
    ⟨p1,by rw [RamFrames.run_array_length r1]; dsimp [wordLength] at hroom; omega⟩
  obtain ⟨σ3,r3,p3⟩ := NativeSplitVectors.weights_spec B n G x R large [1,2*R.card]
    (by simp only [List.length_cons,List.length_nil]; dsimp [wordLength] at hlen; omega) σ2
    ⟨p2.1,p2.2.1,by simpa using p2.2.2,
      by simp only [List.length_cons,List.length_nil]; rw [RamFrames.run_array_length (r1.seq r2)]; dsimp [wordLength] at hroom; omega⟩
  let front := [1,2*R.card]++RamUnsignedBuffer.encode (List.replicate (2*R.card) 1)
  have hf : front.length=2+4*R.card := by
    simp only [front,List.length_append,List.length_cons,List.length_nil,RamUnsignedBuffer.length_encode,List.length_replicate]
    ring
  have hlen' : front.length+2*((2*R.card)*(2*R.card))=wordLength R.card := by rw [hf]; dsimp [wordLength]; ring
  obtain ⟨τ,r4,p4⟩ := NativeSplitVectors.matrix_spec B M n G x R large front hM hsmall
    (by rw [hlen']; omega) hx hl σ3
    ⟨p3.1,p3.2.1,by simpa only [hf,List.length_cons,List.length_nil] using p3.2.2,
      by rw [hlen',RamFrames.run_array_length (r1.seq (r2.seq r3))]; exact hroom⟩
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by nlinarith only []),p4.1,?_,?_⟩
  · simpa only [NativeSplitVectors.input_eq,front] using p4.2.1
  · simpa only [hlen'] using p4.2.2

end Lax263307Proofs.NativeSplitInput
