import Lax263307Proofs.NativeQuadraticVector
import Lax263307Proofs.NativeSignedSum
import Lax263307Proofs.NativeSlice

namespace Lax263307Proofs.NativeQuadraticSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic NativeQuadraticTerms

def height (M n : ℕ) : ℕ := (2*M^2)^(n*n+1)

def cost (M n : ℕ) : ℕ :=
  (36*(M^2).size+36*((height M n)^2).size+369)*(n*n)+44

def prepareSum : Com := .seq (.assign "slice.start" (.lit 0))
  (.seq (.assign "fill.length" (.mul (.lit 3) (.var "quadratic.count")))
    (.assign "sum.count" (.var "quadratic.count")))

def command : Com := .seq NativeQuadraticVector.command
  (.seq prepareSum (.seq (NativeSlice.command "lp.word" "sum.input") NativeSignedSum.command))

/-- Compute the exact ordered edge-product sum from the native graph
and rational vertex vector. The accumulator height is derived from
the input heights, and the graph and source vector survive the call. -/
theorem command_spec (B M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n → ℚ)
    (hM : 1≤M) (hB : 2*M^2+3<B) (hH : 2*(height M n)^2+3<B)
    (hs : 3*(n*n)+3*n+10<B) (ha : ∀ j,Bounded M (a j)) :
    Spec B (fun σ => Context G a σ ∧ 3*(n*n)<(σ.arrs "lp.word").length ∧
      3*(n*n)≤(σ.arrs "sum.input").length) command
      (fun _ τ => Context G a τ ∧
        RamRational.FractionOutput (∑ u,∑ v,if G.Adj u v then a u*a v else 0) τ)
      (cost M n) := by
  have hlen : (terms G a).length=n*n := List.length_ofFn
  have hwlen : (NativeRationalTabulate.words (terms G a)).length=3*(n*n) := by
    rw [NativeRationalTabulate.words_length,hlen]
  have hterms : ∀ x∈terms G a,Bounded (M^2) x := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact NativeQuadraticVector.height M n G a hM ha i
  have hprepare : Spec B (fun σ => σ.vars "quadratic.count"=n*n) prepareSum
      (fun _ τ => τ.vars "slice.start"=0 ∧ τ.vars "fill.length"=3*(n*n) ∧ τ.vars "sum.count"=n*n) 8 := by
    run_vcg
    all_goals simp_all
  rintro σ ⟨hc,hO,hS⟩
  obtain ⟨ν,r1,p1⟩ := NativeQuadraticVector.command_spec B M n G a hM hB hs ha σ ⟨hc,hO⟩
  obtain ⟨μ,r2,p2⟩ := hprepare ν p1.1.2
  have hp : Prefix (NativeRationalTabulate.words (terms G a)) "lp.word" μ := by
    simpa only [Prefix,r2.frame_arr "lp.word" (by decide)] using p1.2.1
  have hwords : ∀ v∈NativeRationalTabulate.words (terms G a),v<B := by
    simpa only [terms,NativeRationalTabulate.words,Lax109476.RationalEncoding.encodeVector] using
      NativeRationalBounds.vector_words B (M^2) (n*n) (term G a) (by omega) (by omega)
        (NativeQuadraticVector.height M n G a hM ha)
  obtain ⟨ξ,r3,p3⟩ := NativeSlice.command_spec B "lp.word" "sum.input" []
    (NativeRationalTabulate.words (terms G a)) [] (by decide)
    (by rw [List.length_nil,hwlen]; omega) hwords μ
    ⟨⟨by simpa using hp,by simpa using p2.1⟩,by simpa only [hwlen] using p2.2.1,
      by rw [hwlen,RamFrames.run_array_length (r1.seq r2)]; exact hS⟩
  have hcount : ξ.vars "sum.count"=(terms G a).length := by
    rw [hlen]
    exact (r3.frame_var "sum.count" (by decide)).trans p2.2.2
  obtain ⟨τ,r4,p4⟩ := NativeSignedSum.bounded_spec B (M^2) (terms G a) (by nlinarith)
    (by simpa only [hlen,height] using hH) (by rw [hlen]; omega) hterms ξ ⟨p3.2,hcount⟩
  have rr := r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr.mono (by rw [hwlen,hlen]; dsimp [cost,height]; nlinarith),?_,?_⟩
  · simpa only [Context,NativeCutRead.Context,Prefix,rr.frame_arr "cut.source" (by decide),
      rr.frame_arr "search.graph" (by decide),rr.frame_var "projection.n" (by decide)] using hc
  · simpa only [terms_sum] using p4.2

end Lax263307Proofs.NativeQuadraticSum
