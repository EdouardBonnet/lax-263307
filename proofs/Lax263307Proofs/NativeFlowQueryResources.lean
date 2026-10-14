import Lax263307Proofs.NativeSplitOracle

namespace Lax263307Proofs.NativeFlowQueryResources

open Lax455465Proofs
open Lax759944.BinaryWordEncoding
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

theorem encode_words (M : ℕ) (qs : List ℚ≥0) (hq : ∀ q∈qs,q.num≤M ∧ q.den≤M) :
    ∀ z∈RamUnsignedBuffer.encode qs,z≤M := by
  intro z hz
  simp only [RamUnsignedBuffer.encode,List.mem_flatMap] at hz
  obtain ⟨q,hmem,hz⟩ := hz
  simp only [Lax455465.RationalEncoding.encodeRational,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl
  · exact (hq q hmem).1
  · exact (hq q hmem).2

theorem query_words (n h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0)
    (hx : ∀ v,Bounded (2^h) (x v : ℚ)) (hl : Bounded (2^h) (large : ℚ)) :
    ∀ z∈NativeSplitOracle.query G x R large,z≤2^(h+n+2) := by
  have hR := NativeMaskUnpack.card_bound R
  have hp : 2^h≤2^(h+n+2) := Nat.pow_le_pow_right (by decide) (by omega)
  have htwo : 2*R.card≤2^(h+n+2) := by
    have hn : n≤2^n := (Nat.lt_two_pow_self).le
    have hh : 2^(n+1)≤2^(h+n+2) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at hh
    omega
  have hM : 1≤2^h := Nat.one_le_two_pow
  have hw := encode_words (2^h) (List.replicate (2*R.card) (1 : ℚ≥0))
    (by intro q hq; have he : q=1 := List.eq_of_mem_replicate hq; subst q; simpa using And.intro hM hM)
  have hm := encode_words (2^h) (NativeSplitVectors.entries G x R large) (by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    simpa only [Bounded,NNRat.natAbs_num_coe,NNRat.den_coe] using
      NativeSplitEntry.height (2^h) R.card (restriction G R) (fun v => x (label R v)) large hM
        (fun v => hx (label R v)) hl (NativeBlowUp.row i) (NativeBlowUp.col i))
  intro z hz
  simp only [NativeSplitOracle.query,NativeSplitVectors.input_eq,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with ((rfl | rfl) | hz) | hz
  · exact Nat.one_le_two_pow
  · exact htwo
  · exact (hw z hz).trans hp
  · exact (hm z hz).trans hp

def sizeBound (n h : ℕ) : ℕ := NativeSplitInput.wordLength n*(h+n+4)

theorem query_size (n h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0)
    (hx : ∀ v,Bounded (2^h) (x v : ℚ)) (hl : Bounded (2^h) (large : ℚ)) :
    bitSize (NativeSplitOracle.query G x R large)≤sizeBound n h := by
  have hs := WordSize.bounded_size (NativeSplitOracle.query G x R large) (h+n+3)
    (by
      intro z hz
      apply Nat.size_le.mpr
      have hh := query_words n h G x R large hx hl z hz
      have hp := Nat.two_pow_pos (h+n+2)
      rw [show h+n+3=(h+n+2)+1 by omega,pow_succ]
      omega)
  have hR := NativeMaskUnpack.card_bound R
  have hlens : NativeSplitInput.wordLength R.card≤NativeSplitInput.wordLength n := by
    dsimp [NativeSplitInput.wordLength]
    nlinarith only [hR,Nat.mul_le_mul hR hR]
  simp only [NativeSplitOracle.query,NativeSplitInput.input_length] at hs
  exact hs.trans (Nat.mul_le_mul_right (h+n+4) hlens)

theorem eval_mono (P : Polynomial ℕ) {x y : ℕ} (h : x≤y) : P.eval x≤P.eval y := by
  obtain ⟨cs,hcs⟩ := RamPolynomial.exists_coefficients P
  simpa only [hcs] using RamPolynomial.value_mono cs h

end Lax263307Proofs.NativeFlowQueryResources
