import Lax263307Proofs.NativeSplitEntry
import Lax263307Proofs.NativeMatrixOrder
import Lax455465Proofs.RamUnsignedVector

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeSplitVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic NativeSplitEntry
open scoped NNRat

def entries {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) : List ℚ≥0 :=
  List.ofFn fun i : Fin ((2*R.card)*(2*R.card)) =>
    (splitInstance (restriction G R) (fun v => x (label R v)) large).capacity
      (NativeBlowUp.row i) (NativeBlowUp.col i)

def matrix : Com := RamUnsignedVector.command "split.i" "split.count" "lp.word" "lp.position" NativeSplitEntry.command

theorem matrix_spec (B M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) (front : List ℕ)
    (hM : 1≤M) (hB : 4*n*n+6*n+M+20<B)
    (hf : front.length+2*((2*R.card)*(2*R.card))+2<B)
    (hx : ∀ v,Bounded M (x v : ℚ)) (hl : Bounded M (large : ℚ)) :
    Spec B (fun σ => Data G x R large σ ∧ Prefix front "lp.word" σ ∧ σ.vars "lp.position"=front.length ∧
      front.length+2*((2*R.card)*(2*R.card))<(σ.arrs "lp.word").length) matrix
      (fun _ τ => Data G x R large τ ∧ Prefix (front++RamUnsignedBuffer.encode (entries G x R large)) "lp.word" τ ∧
        τ.vars "lp.position"=front.length+2*((2*R.card)*(2*R.card))) (122*((2*R.card)*(2*R.card))+6) := by
  have hh (i : Fin ((2*R.card)*(2*R.card))) := NativeSplitEntry.height M R.card (restriction G R)
    (fun v => x (label R v)) large hM (fun v => hx (label R v)) hl (NativeBlowUp.row i) (NativeBlowUp.col i)
  have hv := RamUnsignedVector.command_spec B 100 (Data G x R large)
    "split.i" "split.count" "lp.word" "lp.position" (entries G x R large) front NativeSplitEntry.command
    (by omega) (by simpa only [entries,List.length_ofFn] using hf)
    (by intro i hi; simpa only [entries,List.getElem_ofFn,NNRat.natAbs_num_coe] using
      (hh ⟨i,by simpa only [entries,List.length_ofFn] using hi⟩).1.trans_lt (by omega : M<B))
    (by intro i hi; simpa only [entries,List.getElem_ofFn,NNRat.den_coe] using
      (hh ⟨i,by simpa only [entries,List.length_ofFn] using hi⟩).2.trans_lt (by omega : M<B))
    (by intro σ h; simpa only [entries,List.length_ofFn] using h.2.2.2)
    (by
      intro σ k h
      rcases h with ⟨hd,hs,hn,hc⟩
      refine ⟨⟨hd.labels,hd.graph,hd.costs,by simpa using hd.count,by simpa using hd.order⟩,?_,
        by simpa using hn,by simpa using hc⟩
      simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using hs)
    (by intro i hi; simpa only [entries,List.getElem_ofFn] using
      NativeSplitEntry.command_spec B M n G x R large ⟨i,by simpa only [entries,List.length_ofFn] using hi⟩ hB hx hl)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr hd => frame rr hd (by decide) (by decide)) (by decide) (by decide)
  simpa only [matrix,entries,List.length_ofFn,Nat.reduceAdd] using hv

def weights : Com := RamUnsignedVector.command "split.weight.i" "split.order" "lp.word" "lp.position" RamFractionPrimitives.one

theorem weights_spec (B n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) (front : List ℕ)
    (hB : front.length+4*R.card+3<B) :
    Spec B (fun σ => Data G x R large σ ∧ Prefix front "lp.word" σ ∧ σ.vars "lp.position"=front.length ∧
      front.length+4*R.card<(σ.arrs "lp.word").length) weights
      (fun _ τ => Data G x R large τ ∧ Prefix (front++RamUnsignedBuffer.encode (List.replicate (2*R.card) 1)) "lp.word" τ ∧
        τ.vars "lp.position"=front.length+4*R.card) (56*R.card+6) := by
  have hv := RamUnsignedVector.command_spec B 6 (Data G x R large)
    "split.weight.i" "split.order" "lp.word" "lp.position" (List.replicate (2*R.card) (1 : ℚ≥0)) front RamFractionPrimitives.one
    (by omega) (by simp only [List.length_replicate]; omega)
    (by intro i hi; simp; omega) (by intro i hi; simp; omega)
    (by intro σ h; simpa only [List.length_replicate] using h.2.2.1)
    (by
      intro σ k h
      rcases h with ⟨hd,hs,hn,hc⟩
      refine ⟨⟨hd.labels,hd.graph,hd.costs,by simpa using hd.count,by simpa using hd.order⟩,?_,
        by simpa using hn,by simpa using hc⟩
      simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false] using hs)
    (by
      intro i hi σ h
      obtain ⟨τ,rr,ht⟩ := RamFractionPrimitives.one_spec B (by omega) σ trivial
      exact ⟨τ,rr,frame rr h.1 (by decide) (by decide),by simpa using ht⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr hd => frame rr hd (by decide) (by decide)) (by decide) (by decide)
  convert hv using 1 <;> simp only [weights,List.length_replicate] <;> ring

theorem input_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) :
    Lax455465.RationalEncoding.encodeInput .directed (splitInstance (restriction G R) (fun v => x (label R v)) large)=
      ([1,2*R.card]++RamUnsignedBuffer.encode (List.replicate (2*R.card) 1))++
        RamUnsignedBuffer.encode (entries G x R large) := by
  rw [Lax455465.RationalEncoding.encodeInput]
  rw [show entries G x R large=(List.ofFn fun u => List.ofFn
    ((splitInstance (restriction G R) (fun v => x (label R v)) large).capacity u)).flatten from
      NativeMatrixOrder.flatten _ _]
  simp only [splitInstance,List.ofFn_const,RamUnsignedBuffer.encode,List.append_assoc]

end Lax263307Proofs.NativeSplitVectors
