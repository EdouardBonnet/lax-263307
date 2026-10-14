import Lax263307Proofs.NativeConditioningEntry
import Lax263307Proofs.NativeFirstScan

set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

namespace Lax263307Proofs.NativeHeavySearch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeSignedArithmetic NativeCatalogMetadata NativeConditioningEntry

def Output {n : ℕ} : Option (Finset (Fin n)) → Env → Prop
  | none,τ => τ.vars "conditioning.found"=0
  | some A,τ => τ.vars "conditioning.found"=1 ∧ τ.vars "conditioning.choice"=NativeMasks.mask A

def finish : Com := .ite (.lt (.var "scan.result") (.var "catalog.count"))
  (.seq (.assign "conditioning.choice" (.get "catalog.mask" (.var "scan.result")))
    (.assign "conditioning.found" (.lit 1)))
  (.assign "conditioning.found" (.lit 0))

theorem selection (n r k p : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) : findHeavyConditioning G k p y=
    if h : NativeConditioningOrder.first G k p y<N n r then
      some (atIndex n r ⟨NativeConditioningOrder.first G k p y,h⟩) else none := by
  rw [←NativeConditioningOrder.selected,List.find?_eq_getElem?_findIdx]
  change ((List.finRange (N n r))[NativeConditioningOrder.first G k p y]?).map (atIndex n r)=_
  split_ifs with h
  · rw [List.getElem?_eq_getElem (by simpa using h),List.getElem_finRange]
    rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h)]
    rfl

theorem finish_spec (B n r k p : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (hN : N n r+2<B) (hm : 2^n<B) :
    Spec B (fun σ => Data G y σ ∧ σ.vars "scan.result"=NativeConditioningOrder.first G k p y)
      finish (fun _ τ => Data G y τ ∧ Output (findHeavyConditioning G k p y) τ) 12 := by
  rintro σ ⟨hc,hf⟩
  have hfB : NativeConditioningOrder.first G k p y<B := (NativeConditioningOrder.first_le G k p y).trans_lt (by omega)
  have hv : (Cond.lt (.var "scan.result") (.var "catalog.count")).evalB B σ=
      some (decide (NativeConditioningOrder.first G k p y<N n r)) := evalB_condLt
    (by rw [evalB_var_iff]; exact ⟨hf.symm,hf ▸ hfB⟩)
    (by rw [evalB_var_iff]; exact ⟨hc.moments.2.2.symm,hc.moments.2.2 ▸ (by omega : N n r<B)⟩)
  by_cases h : NativeConditioningOrder.first G k p y<N n r
  · let i : Fin (N n r) := ⟨NativeConditioningOrder.first G k p y,h⟩
    have hilen : i.val<(Lax263307.NativeCatalog.words n r).length := by
      simpa only [Lax263307.NativeCatalog.words,List.length_map] using i.isLt
    have hg := hc.moments.1 i.val hilen
    have hw := NativeMomentAccess.mask_word n r i
    rw [List.getElem?_eq_getElem hilen] at hw
    rw [Option.some.inj hw] at hg
    let ν := σ.setVar "conditioning.choice" (NativeMasks.mask (atIndex n r i))
    have r1 : Run B (.assign "conditioning.choice" (.get "catalog.mask" (.var "scan.result"))) σ ν 3 :=
      Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hf.symm,hf ▸ hfB⟩) hg ((NativeMasks.mask_bound _).trans hm))
    let τ := ν.setVar "conditioning.found" 1
    have r2 : Run B (.assign "conditioning.found" (.lit 1)) ν τ 2 := Run.assign (evalB_lit (by omega))
    have rr : Run B finish σ τ 12 := (Run.ite_true (by simpa only [h,decide_true] using hv) (r1.seq r2)).mono (by decide)
    exact ⟨τ,rr,frame rr hc (by decide) (by decide),by rw [selection, dif_pos h]; simp [Output,τ,ν,i]⟩
  · let τ := σ.setVar "conditioning.found" 0
    have r1 : Run B (.assign "conditioning.found" (.lit 0)) σ τ 2 := Run.assign (evalB_lit (by omega))
    have rr : Run B finish σ τ 12 := (Run.ite_false (by simpa only [h,decide_false] using hv) r1).mono (by decide)
    exact ⟨τ,rr,frame rr hc (by decide) (by decide),by rw [selection,dif_neg h]; simp [Output,τ]⟩

def command : Com := .seq NativeConditioningFloor.command
  (.seq (.assign "scan.count" (.var "catalog.count"))
    (.seq (NativeFirstScan.command NativeConditioningEntry.command) finish))

def cost (M n r : ℕ) := 12*n.size+12*r+50+(NativeConditioningEntry.cost M n r+18)*N n r

/-- Native exhaustive search in the exact order of the functional
conditioning oracle. No numerical predicate or subset selection is
supplied to the program as an oracle. -/
theorem command_spec (B M n r k p : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (hn : 0<n) (hp : 0<p) (hM : 1≤M)
    (hN : 3*N n r+10<B) (hs : 3*(n*n)+3*n+r+10<B) (hm : 2^n<B)
    (hB : 2*M^2+3<B) (hH : 2*(NativeQuadraticSum.height M n)^2+3<B)
    (hy : ∀ T,Bounded M (y T))
    (htest : NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
      M (NativeQuadraticSum.height M n)<B)
    (hfloor : NativeConditioningFloor.base n p+NativeConditioningFloor.base n p^r+n+p+r+10<B) :
    Spec B (fun σ => Data G y σ ∧ σ.vars "conditioning.k"=k ∧ σ.vars "conditioning.p"=p)
      command (fun _ τ => Data G y τ ∧ Output (findHeavyConditioning G k p y) τ) (cost M n r) := by
  let P : Env → Prop := fun σ => Data G y σ ∧ Parameters k p (NativeConditioningFloor.base n p^r) σ ∧ σ.vars "scan.count"=N n r
  have hi : ∀ σ t,P σ → P (σ.setVar "scan.i" t) := by
    rintro σ t ⟨d,hp,hc⟩
    refine ⟨?_,by simpa only [Parameters,vars_setVar,String.reduceEq,if_false] using hp,by simpa using hc⟩
    rcases d with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    constructor <;> simp_all [NativeMomentValue.Context,Prefix]
  have hr : ∀ σ t,P σ → P (σ.setVar "scan.result" t) := by
    rintro σ t ⟨d,hp,hc⟩
    refine ⟨?_,by simpa only [Parameters,vars_setVar,String.reduceEq,if_false] using hp,by simpa using hc⟩
    rcases d with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
    constructor <;> simp_all [NativeMomentValue.Context,Prefix]
  have hscan := NativeFirstScan.command_spec B (N n r) (NativeConditioningOrder.first G k p y)
    (NativeConditioningEntry.cost M n r) P NativeConditioningEntry.command (NativeConditioningOrder.accepted G k p y)
    (by omega) (NativeConditioningOrder.first_le G k p y) (NativeConditioningOrder.before G k p y)
    (NativeConditioningOrder.at_first G k p y) (fun _ h => h.2.2) hi hr
    (by rintro σ τ rr ⟨hd,hp,hc⟩; exact ⟨frame rr hd (by decide) (by decide),
      parameters_frame rr hp (by decide),(rr.frame_var "scan.count" (by decide)).trans hc⟩)
    (by decide) (by decide)
    (by
      rintro i σ ⟨⟨hd,hparams,hc⟩,hi⟩
      obtain ⟨τ,rr,d,pp,ha⟩ := NativeConditioningEntry.command_spec B M n r k p G y i hn hp hM hN hs hm hB hH hy htest σ ⟨hd,hparams,hi⟩
      exact ⟨τ,rr,⟨d,pp,(rr.frame_var "scan.count" (by decide)).trans hc⟩,ha⟩)
  rintro σ ⟨hc,hk,hpσ⟩
  obtain ⟨ν,r1,p1⟩ := NativeConditioningFloor.command_spec B n p r hn hp hfloor σ ⟨hc.order,hpσ,hc.level⟩
  have d1 := frame r1 hc (by decide) (by decide)
  let μ := ν.setVar "scan.count" (N n r)
  have r2 : Run B (.assign "scan.count" (.var "catalog.count")) ν μ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨d1.moments.2.2.symm,d1.moments.2.2 ▸ (by omega : N n r<B)⟩)
  have r12 := r1.seq r2
  have hmP : P μ := ⟨frame r12 hc (by decide) (by decide),
    ⟨(r12.frame_var "conditioning.k" (by decide)).trans hk,
      (r12.frame_var "conditioning.p" (by decide)).trans hpσ,
      (r2.frame_var "conditioning.floorDen" (by decide)).trans p1⟩,by simp [μ]⟩
  obtain ⟨ξ,r3,p3⟩ := hscan μ hmP
  obtain ⟨τ,r4,p4⟩ := finish_spec B n r k p G y (by omega) hm ξ ⟨p3.1.1,p3.2⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by dsimp [cost]; omega),p4⟩

end Lax263307Proofs.NativeHeavySearch
