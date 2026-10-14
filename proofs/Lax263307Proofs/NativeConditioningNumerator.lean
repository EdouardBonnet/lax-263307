import Lax263307Proofs.NativeConditioningVector
import Lax263307Proofs.NativeQuadraticSum

set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeConditioningNumerator

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic NativeCatalogMetadata

def extensions {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) (v : Fin n) : ℚ :=
  rationalValue y (insert v A)

def Context {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) (σ : Env) : Prop :=
  NativeConditioningVector.Data y A σ ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ

theorem frame {B n r K : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) {c : Com} {σ τ : Env}
    (rr : Run B c σ τ K) (hc : Context G y A σ)
    (h0 : "catalog.mask"∉c.warrs) (h1 : "near.moments"∉c.warrs) (h2 : "search.graph"∉c.warrs)
    (h3 : "catalog.count"∉c.wvars) (h4 : "conditioning.mask"∉c.wvars) (h5 : "graph.n"∉c.wvars) :
    Context G y A τ := by
  exact ⟨NativeConditioningVector.frame rr hc.1 h0 h1 h3 h4 h5,
    by simpa only [Prefix,rr.frame_arr "search.graph" h2] using hc.2⟩

theorem extensions_bounded (M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n))
    (hA : A.card≤r) (hy : ∀ T,Bounded M (y T)) (v : Fin n) : Bounded M (extensions y A v) := by
  have hh : (insert v A).card≤r+2 := (Finset.card_insert_le v A).trans (by omega)
  simpa only [extensions,rationalValue,dif_pos hh] using hy ⟨insert v A,hh⟩

def prepareCopy : Com := .seq (.assign "projection.n" (.var "graph.n"))
  (.seq (.assign "slice.start" (.lit 0)) (.assign "fill.length" (.mul (.lit 3) (.var "graph.n"))))

def prepare : Com := .seq NativeConditioningVector.command
  (.seq prepareCopy (NativeSlice.command "lp.word" "cut.source"))

def command : Com := .seq prepare NativeQuadraticSum.command

def cost (M n r : ℕ) : ℕ := (17*N n r+120)*n+22+NativeQuadraticSum.cost M n

theorem prepare_spec (B M n r : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) (hA : A.card≤r)
    (hN : 3*N n r+10<B) (hn : 3*n+3<B) (hm : 2^n<B) (hM : M<B)
    (hy : ∀ T,Bounded M (y T)) :
    Spec B (fun σ => Context G y A σ ∧ 3*n<(σ.arrs "lp.word").length ∧
      3*n≤(σ.arrs "cut.source").length) prepare
      (fun _ τ => Context G y A τ ∧ NativeQuadraticTerms.Context G (extensions y A) τ)
      ((17*N n r+120)*n+22) := by
  have hlen : (encodeVector (extensions y A)).length=3*n := by
    change (RamVectorEncoding.encode (List.ofFn (extensions y A))).length=_
    rw [RamVectorEncoding.length_encode,List.length_ofFn]
  have hprepare : Spec B (fun σ => σ.vars "graph.n"=n) prepareCopy
      (fun _ τ => τ.vars "projection.n"=n ∧ τ.vars "slice.start"=0 ∧ τ.vars "fill.length"=3*n) 8 := by
    run_vcg
    all_goals simp_all
  rintro σ ⟨hc,hO,hC⟩
  obtain ⟨ν,r1,p1⟩ := NativeConditioningVector.command_spec B M n r y A hA hN hn hm hM hy σ ⟨hc.1,hO⟩
  obtain ⟨μ,r2,p2⟩ := hprepare ν p1.1.2.2
  have hp : Prefix (encodeVector (extensions y A)) "lp.word" μ := by
    change Prefix (encodeVector (fun v => rationalValue y (insert v A))) "lp.word" μ
    simpa only [Prefix,r2.frame_arr "lp.word" (by decide)] using p1.2.1
  obtain ⟨τ,r3,p3⟩ := NativeSlice.command_spec B "lp.word" "cut.source" [] (encodeVector (extensions y A)) []
    (by decide) (by rw [List.length_nil,hlen]; omega)
    (NativeRationalBounds.vector_words B M n (extensions y A) (by omega) hM (extensions_bounded M n r y A hA hy)) μ
    ⟨⟨by simpa using hp,by simpa using p2.2.1⟩,by simpa only [hlen] using p2.2.2,
      by rw [hlen,RamFrames.run_array_length (r1.seq r2)]; exact hC⟩
  have rr := r1.seq (r2.seq r3)
  have ht := frame G y A rr hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨τ,rr.mono (by rw [hlen]; nlinarith),ht,
    ⟨p3.2,(r3.frame_var "projection.n" (by decide)).trans p2.1⟩,ht.2⟩

/-- The complete exact edge numerator for one conditioning candidate,
starting with the stored near point and the actual subset mask. -/
theorem command_spec (B M n r : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) (hA : A.card≤r) (hM : 1≤M)
    (hN : 3*N n r+10<B) (hn : 3*(n*n)+3*n+10<B) (hm : 2^n<B)
    (hB : 2*M^2+3<B) (hH : 2*(NativeQuadraticSum.height M n)^2+3<B)
    (hy : ∀ T,Bounded M (y T)) :
    Spec B (fun σ => Context G y A σ ∧ 3*n+3*(n*n)<(σ.arrs "lp.word").length ∧
      3*n≤(σ.arrs "cut.source").length ∧ 3*(n*n)≤(σ.arrs "sum.input").length) command
      (fun _ τ => Context G y A τ ∧ RamRational.FractionOutput (edgeNumerator G y A) τ)
      (cost M n r) := by
  rintro σ ⟨hc,hO,hC,hS⟩
  obtain ⟨ν,r1,p1⟩ := prepare_spec B M n r G y A hA hN (by omega) hm (by nlinarith) hy σ ⟨hc,by omega,hC⟩
  obtain ⟨τ,r2,p2⟩ := NativeQuadraticSum.command_spec B M n G (extensions y A) hM hB hH hn
    (extensions_bounded M n r y A hA hy) ν
    ⟨p1.2,by rw [RamFrames.run_array_length r1]; omega,by rwa [RamFrames.run_array_length r1]⟩
  exact ⟨τ,r1.seq r2,frame G y A r2 p1.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by simpa only [edgeNumerator,extensions] using p2.2⟩

end Lax263307Proofs.NativeConditioningNumerator
