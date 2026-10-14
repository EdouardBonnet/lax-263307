import Lax263307Proofs.NativeConditioningResources
import Lax263307Proofs.NativeConditioningOrder

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeConditioningEntry

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 RationalConditioning HeavyRationalConditioning
open NativeSignedArithmetic NativeCatalogMetadata

structure Data {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (σ : Env) : Prop where
  moments : NativeMomentValue.Context y σ
  cards : Prefix (NativeCatalogMetadata.cards n r) "catalog.card" σ
  graph : Prefix (NativeWeightReduction.adjacency G) "search.graph" σ
  order : σ.vars "graph.n"=n
  level : σ.vars "moment.r"=r
  outputRoom : 3*n+3*(n*n)<(σ.arrs "lp.word").length
  copyRoom : 3*n≤(σ.arrs "cut.source").length
  sumRoom : 3*(n*n)≤(σ.arrs "sum.input").length

def Parameters (k p D : ℕ) (σ : Env) : Prop :=
  σ.vars "conditioning.k"=k ∧ σ.vars "conditioning.p"=p ∧ σ.vars "conditioning.floorDen"=D

theorem frame {B n r K : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {y : RationalVector n r} {c : Com} {σ τ : Env} (rr : Run B c σ τ K) (hc : Data G y σ)
    (ha : ∀ s∈["catalog.mask","near.moments","catalog.card","search.graph"],s∉c.warrs)
    (hv : ∀ s∈["catalog.count","graph.n","moment.r"],s∉c.wvars) : Data G y τ := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [NativeMomentValue.Context,Prefix,
      rr.frame_arr "catalog.mask" (ha _ (by simp)),rr.frame_arr "near.moments" (ha _ (by simp)),
      rr.frame_var "catalog.count" (hv _ (by simp))] using hc.moments
  · simpa only [Prefix,rr.frame_arr "catalog.card" (ha _ (by simp))] using hc.cards
  · simpa only [Prefix,rr.frame_arr "search.graph" (ha _ (by simp))] using hc.graph
  · exact (rr.frame_var "graph.n" (hv _ (by simp))).trans hc.order
  · exact (rr.frame_var "moment.r" (hv _ (by simp))).trans hc.level
  · simpa only [RamFrames.run_array_length rr] using hc.outputRoom
  · simpa only [RamFrames.run_array_length rr] using hc.copyRoom
  · simpa only [RamFrames.run_array_length rr] using hc.sumRoom

theorem parameters_frame {B K k p D : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    (hc : Parameters k p D σ)
    (hv : ∀ s∈["conditioning.k","conditioning.p","conditioning.floorDen"],s∉c.wvars) :
    Parameters k p D τ := by
  simpa only [Parameters,rr.frame_var "conditioning.k" (hv _ (by simp)),
    rr.frame_var "conditioning.p" (hv _ (by simp)),rr.frame_var "conditioning.floorDen" (hv _ (by simp))] using hc

def read : Com := .seq
  (.assign "conditioning.mask" (.get "catalog.mask" (.var "scan.i")))
  (.assign "conditioning.card" (.get "catalog.card" (.var "scan.i")))

theorem read_spec (B n r : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (i : Fin (N n r)) (hN : N n r<B) (hn : n<B) (hm : 2^n<B) :
    Spec B (fun σ => Data G y σ ∧ σ.vars "scan.i"=i.val) read
      (fun _ τ => Data G y τ ∧ τ.vars "conditioning.mask"=NativeMasks.mask (atIndex n r i) ∧
        τ.vars "conditioning.card"=(atIndex n r i).card) 6 := by
  rintro σ ⟨hc,hi⟩
  have hilen : i.val<(Lax263307.NativeCatalog.words n r).length := by
    simpa only [Lax263307.NativeCatalog.words,List.length_map] using i.isLt
  have hg := hc.moments.1 i.val hilen
  have hw := NativeMomentAccess.mask_word n r i
  rw [List.getElem?_eq_getElem (by simpa only [Lax263307.NativeCatalog.words,List.length_map] using i.isLt)] at hw
  have he : (Lax263307.NativeCatalog.words n r)[i.val]=NativeMasks.mask (atIndex n r i) := Option.some.inj hw
  rw [he] at hg
  let ν := σ.setVar "conditioning.mask" (NativeMasks.mask (atIndex n r i))
  have r1 : Run B (.assign "conditioning.mask" (.get "catalog.mask" (.var "scan.i"))) σ ν 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ i.isLt.trans hN⟩)
      hg ((NativeMasks.mask_bound _).trans hm))
  have hcard := hc.cards i.val (by simpa only [NativeCatalogMetadata.cards,List.length_ofFn] using i.isLt)
  simp only [NativeCatalogMetadata.cards,List.getElem_ofFn] at hcard
  let τ := ν.setVar "conditioning.card" (atIndex n r i).card
  have r2 : Run B (.assign "conditioning.card" (.get "catalog.card" (.var "scan.i"))) ν τ 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; simpa only [ν,vars_setVar,String.reduceEq,if_false] using
      (show i.val=σ.vars "scan.i" ∧ σ.vars "scan.i"<B from ⟨hi.symm,hi ▸ i.isLt.trans hN⟩))
      hcard ((NativeMaskUnpack.card_bound _).trans_lt hn))
  exact ⟨τ,r1.seq r2,frame (r1.seq r2) hc (by decide) (by decide),by simp [τ,ν],by simp [τ]⟩

def choose : Com := .ite (.lt (.var "moment.r") (.var "conditioning.card"))
  (.assign "conditioning.passes" (.lit 0)) NativeHeavyCandidate.command

def command : Com := .seq read (.seq choose (.assign "scan.accepted" (.var "conditioning.passes")))

def cost (M n r : ℕ) := NativeHeavyCandidate.cost M n r+12

theorem command_spec (B M n r k p : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (y : RationalVector n r) (i : Fin (N n r)) (hn : 0<n) (hp : 0<p)
    (hM : 1≤M) (hN : 3*N n r+10<B) (hs : 3*(n*n)+3*n+r+10<B)
    (hm : 2^n<B) (hB : 2*M^2+3<B) (hH : 2*(NativeQuadraticSum.height M n)^2+3<B)
    (hy : ∀ T,Bounded M (y T))
    (htest : NativeConditioningResources.testBound k p (NativeConditioningFloor.base n p^r)
      M (NativeQuadraticSum.height M n)<B) :
    Spec B (fun σ => Data G y σ ∧ Parameters k p (NativeConditioningFloor.base n p^r) σ ∧ σ.vars "scan.i"=i.val)
      command (fun _ τ => Data G y τ ∧ Parameters k p (NativeConditioningFloor.base n p^r) τ ∧
        τ.vars "scan.accepted"=if NativeConditioningOrder.accepted G k p y i then 1 else 0) (cost M n r) := by
  rintro σ ⟨hc,hparams,hi⟩
  obtain ⟨ν,r1,d1,hmν,hcardν⟩ := read_spec B n r G y i (by omega) (by omega) hm σ ⟨hc,hi⟩
  have hcardB : (atIndex n r i).card<B := (NativeMaskUnpack.card_bound _).trans_lt (by omega)
  have hv : (Cond.lt (.var "moment.r") (.var "conditioning.card")).evalB B ν=
      some (decide (r<(atIndex n r i).card)) :=
    evalB_condLt
      (by rw [evalB_var_iff]; exact ⟨d1.level.symm,d1.level ▸ (by omega : r<B)⟩)
      (by rw [evalB_var_iff]; exact ⟨hcardν.symm,hcardν ▸ hcardB⟩)
  have hpar1 := parameters_frame r1 hparams (by decide)
  have hcand : ∃ μ,Run B choose ν μ (NativeHeavyCandidate.cost M n r+4) ∧
      μ.vars "conditioning.passes"=if NativeConditioningOrder.accepted G k p y i then 1 else 0 := by
    by_cases hA : (atIndex n r i).card≤r
    · obtain ⟨μ,rr,pp⟩ := NativeHeavyCandidate.command_spec B M n r k p G y (atIndex n r i)
        hn hp hA hM hN (by omega) hm hB hH hy
        ((NativeConditioningResources.candidate_test M n r k p G y (atIndex n r i) hM hA hy).trans_lt htest) ν
        ⟨⟨⟨d1.moments,hmν,d1.order⟩,d1.graph⟩,
          hpar1.1,hpar1.2.1,hpar1.2.2,d1.outputRoom,d1.copyRoom,d1.sumRoom⟩
      refine ⟨μ,(Run.ite_false (by simpa only [not_lt.mpr hA,decide_false] using hv) rr).mono
        (by simp only [Cond.size,Expr.size]; omega),?_⟩
      simpa [NativeConditioningOrder.accepted,NativeConditioningOrder.test,hA] using pp.2
    · let μ := ν.setVar "conditioning.passes" 0
      have rr : Run B (.assign "conditioning.passes" (.lit 0)) ν μ 2 := Run.assign (evalB_lit (by omega))
      refine ⟨μ,(Run.ite_true (by simpa only [Nat.lt_of_not_ge hA,decide_true] using hv) rr).mono
        (by dsimp [Cond.size,Expr.size,NativeHeavyCandidate.cost]; omega),?_⟩
      simp [μ,NativeConditioningOrder.accepted,NativeConditioningOrder.test,hA]
  obtain ⟨μ,r2,hpass⟩ := hcand
  let τ := μ.setVar "scan.accepted" (if NativeConditioningOrder.accepted G k p y i then 1 else 0)
  have r3 : Run B (.assign "scan.accepted" (.var "conditioning.passes")) μ τ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hpass.symm,hpass ▸ (by split_ifs <;> omega)⟩)
  have rr := r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by dsimp [cost]; omega),frame rr hc (by decide) (by decide),
    parameters_frame rr hparams (by decide),by simp [τ]⟩

end Lax263307Proofs.NativeConditioningEntry
