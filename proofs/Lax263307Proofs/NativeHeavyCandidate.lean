import Lax263307Proofs.NativeConditioningNumerator
import Lax263307Proofs.NativeConditioningFloor
import Lax263307Proofs.NativeConditioningTest

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeHeavyCandidate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeSignedArithmetic NativeCatalogMetadata NativeConditioningNumerator

theorem edge_bounded (M n r : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) (hM : 1≤M) (hA : A.card≤r)
    (hy : ∀ T,Bounded M (y T)) : Bounded (NativeQuadraticSum.height M n) (edgeNumerator G y A) := by
  have hext := extensions_bounded M n r y A hA hy
  have hterms : ∀ q∈NativeQuadraticTerms.terms G (extensions y A),Bounded (M^2) q := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact NativeQuadraticVector.height M n G (extensions y A) hM hext i
  have hlen : (NativeQuadraticTerms.terms G (extensions y A)).length=n*n := List.length_ofFn
  have hh := NativeSumHeight.uniform_partial (M^2) (NativeQuadraticTerms.terms G (extensions y A))
    (by nlinarith) hterms (NativeQuadraticTerms.terms G (extensions y A)).length
  rw [List.take_length] at hh
  simpa only [hlen,NativeQuadraticTerms.terms_sum,NativeQuadraticSum.height,
    extensions,edgeNumerator] using hh

def command : Com := .seq (.assign "lookup.key" (.var "conditioning.mask"))
  (.seq NativeMomentValue.command (.seq (save "conditioning.a")
    (.seq NativeConditioningNumerator.command (.seq (save "conditioning.edge") NativeConditioningTest.command))))

def cost (M n r : ℕ) : ℕ := 17*N n r+91+NativeConditioningNumerator.cost M n r

/-- The full native test for one conditioning candidate, reading its
moment and all edge terms from the stored near point. The output bit
is exactly the predicate used by findHeavyConditioning. -/
theorem command_spec (B M n r k p : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (A : Finset (Fin n)) (hn : 0<n) (hp : 0<p)
    (hA : A.card≤r) (hM : 1≤M) (hN : 3*N n r+10<B) (hs : 3*(n*n)+3*n+10<B)
    (hm : 2^n<B) (hB : 2*M^2+3<B) (hH : 2*(NativeQuadraticSum.height M n)^2+3<B)
    (hy : ∀ T,Bounded M (y T))
    (htest : NativeConditioningTest.resource k p (NativeConditioningFloor.base n p^r)
      (rationalValue y A).num.natAbs (rationalValue y A).den
      (edgeNumerator G y A).num.natAbs (edgeNumerator G y A).den<B) :
    Spec B (fun σ => Context G y A σ ∧ σ.vars "conditioning.k"=k ∧ σ.vars "conditioning.p"=p ∧
      σ.vars "conditioning.floorDen"=NativeConditioningFloor.base n p^r ∧
      3*n+3*(n*n)<(σ.arrs "lp.word").length ∧ 3*n≤(σ.arrs "cut.source").length ∧
      3*(n*n)≤(σ.arrs "sum.input").length) command
      (fun _ τ => Context G y A τ ∧
        τ.vars "conditioning.passes"=if HeavyPasses G k p y A then 1 else 0) (cost M n r) := by
  have h1 : 1<B := by nlinarith
  have hMB : M<B := by nlinarith
  have hHB : NativeQuadraticSum.height M n<B := by nlinarith
  have hq : Bounded M (rationalValue y A) := by
    have hh : A.card≤r+2 := by omega
    simpa only [rationalValue,dif_pos hh] using hy ⟨A,hh⟩
  have he := edge_bounded M n r G y A hM hA hy
  have hD : 0<NativeConditioningFloor.base n p^r := by dsimp [NativeConditioningFloor.base]; positivity
  rintro σ ⟨hc,hk,hpσ,hDσ,hO,hC,hS⟩
  let σ1 := σ.setVar "lookup.key" (NativeMasks.mask A)
  have r1 : Run B (.assign "lookup.key" (.var "conditioning.mask")) σ σ1 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hc.1.2.1.symm,hc.1.2.1 ▸ (NativeMasks.mask_bound A).trans hm⟩)
  have hc1 := frame G y A r1 hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨σ2,r2,p2⟩ := NativeMomentValue.command_spec B M n r y A (by omega) hN hm hMB hy σ1
    ⟨hc1.1.1,by simp [σ1]⟩
  obtain ⟨σ3,r3,p3⟩ := save_spec B "conditioning.a" (rationalValue y A) h1
    (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) (by decide) σ2 p2.2
  have r123 := r1.seq (r2.seq r3)
  have hc3 := frame G y A r123 hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨σ4,r4,p4⟩ := NativeConditioningNumerator.command_spec B M n r G y A hA hM hN hs hm hB hH hy σ3
    ⟨hc3,by rwa [RamFrames.run_array_length r123],by rwa [RamFrames.run_array_length r123],
      by rwa [RamFrames.run_array_length r123]⟩
  obtain ⟨σ5,r5,p5⟩ := save_spec B "conditioning.edge" (edgeNumerator G y A) h1
    (he.1.trans_lt hHB) (he.2.trans_lt hHB) (by decide) σ4 p4.2
  have hq5 : Stored "conditioning.a" (rationalValue y A) σ5 := by
    simpa only [Stored,String.reduceAppend,(r4.seq r5).frame_var "conditioning.a.s" (by decide),
      (r4.seq r5).frame_var "conditioning.a.n" (by decide),
      (r4.seq r5).frame_var "conditioning.a.d" (by decide)] using p3
  have r12345 := r123.seq (r4.seq r5)
  obtain ⟨τ,r6,p6⟩ := NativeConditioningTest.stored_spec B k p (NativeConditioningFloor.base n p^r)
    (rationalValue y A) (edgeNumerator G y A) hD htest σ5
    ⟨(r12345.frame_var "conditioning.k" (by decide)).trans hk,
      (r12345.frame_var "conditioning.p" (by decide)).trans hpσ,
      (r12345.frame_var "conditioning.floorDen" (by decide)).trans hDσ,hq5,p5⟩
  have rr := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  have hpred : NativeConditioningPredicate.Test k p (NativeConditioningFloor.base n p^r)
      (rationalValue y A) (edgeNumerator G y A) ↔ HeavyPasses G k p y A := by
    simp only [NativeConditioningPredicate.Test,HeavyPasses,Passes,NativeConditioningFloor.floor_value]
    tauto
  exact ⟨τ,rr.mono (by dsimp [cost]; omega),
    frame G y A rr hc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by simpa only [hpred] using p6⟩

end Lax263307Proofs.NativeHeavyCandidate
