import Lax263307Proofs.NativePositiveQuotient
import Lax263307Proofs.NativeConditioningVector
import Lax263307Proofs.NativeSlice
import Lax263307.NearOracle

set_option maxRecDepth 20000
set_option maxHeartbeats 900000

namespace Lax263307Proofs.NativeNearCosts

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic NativeCatalogMetadata

def values {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) (v : Fin n) : ℚ := NearOracle.costs y A v

def Data {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) (σ : Env) : Prop :=
  NativeConditioningVector.Data y A σ ∧ Stored "quotient.denominator" (rationalValue y A) σ

theorem frame {B n r K : ℕ} {y : RationalVector n r} {A : Finset (Fin n)}
    {c : Com} {σ τ : Env} (rr : Run B c σ τ K) (hd : Data y A σ)
    (ha : ∀ s∈["catalog.mask","near.moments"],s∉c.warrs)
    (hv : ∀ s∈["catalog.count","conditioning.mask","graph.n","quotient.denominator.s",
      "quotient.denominator.n","quotient.denominator.d"],s∉c.wvars) : Data y A τ := by
  refine ⟨NativeConditioningVector.frame rr hd.1 (ha _ (by simp)) (ha _ (by simp))
    (hv _ (by simp)) (hv _ (by simp)) (hv _ (by simp)),?_⟩
  simpa only [Stored,String.reduceAppend,rr.frame_var "quotient.denominator.s" (hv _ (by simp)),
    rr.frame_var "quotient.denominator.n" (hv _ (by simp)),
    rr.frame_var "quotient.denominator.d" (hv _ (by simp))] using hd.2

theorem moment_bound (M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n))
    (hA : A.card≤r) (hy : ∀ T,Bounded M (y T)) : Bounded M (rationalValue y A) := by
  have hh : A.card≤r+2 := by omega
  simpa only [rationalValue,dif_pos hh] using hy ⟨A,hh⟩

theorem extension_bound (M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n))
    (hA : A.card≤r) (hy : ∀ T,Bounded M (y T)) (v : Fin n) : Bounded M (rationalValue y (insert v A)) := by
  have hh : (insert v A).card≤r+2 := (Finset.card_insert_le v A).trans (by omega)
  simpa only [rationalValue,dif_pos hh] using hy ⟨insert v A,hh⟩

theorem height (M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n))
    (hM : 1≤M) (hA : A.card≤r) (hy : ∀ T,Bounded M (y T)) (v : Fin n) :
    Bounded (M^2) (values y A v) :=
  NativePositiveQuotient.height M _ _ hM (extension_bound M n r y A hA hy v) (moment_bound M n r y A hA hy)

def read : Com := .seq NativeConditioningVector.read
  (.seq (save "quotient.numerator") NativePositiveQuotient.command)

theorem read_spec (B M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) (v : Fin n)
    (hM : 1≤M) (hA : A.card≤r) (hN : 3*N n r+10<B) (hn : n+2<B) (hm : 2^n<B)
    (hB : 2*M^2+3<B) (hy : ∀ T,Bounded M (y T)) :
    Spec B (fun σ => Data y A σ ∧ σ.vars "conditioning.v"=v.val) read
      (fun _ τ => Data y A τ ∧ RamRational.FractionOutput (values y A v) τ)
      (17*N n r+72*(M^2).size+187) := by
  have h1 : 1<B := by nlinarith
  have hMB : M<B := by nlinarith
  have hv := extension_bound M n r y A hA hy v
  rintro σ ⟨hd,hi⟩
  obtain ⟨ν,r1,p1⟩ := NativeConditioningVector.read_spec B M n r y A v hA hN hn hm hMB hy σ ⟨hd.1,hi⟩
  obtain ⟨μ,r2,p2⟩ := save_spec B "quotient.numerator" (rationalValue y (insert v A)) h1
    (hv.1.trans_lt hMB) (hv.2.trans_lt hMB) (by decide) ν p1.2
  have hdμ := frame (r1.seq r2) hd (by decide) (by decide)
  obtain ⟨τ,r3,p3⟩ := NativePositiveQuotient.command_spec B M (rationalValue y (insert v A)) (rationalValue y A)
    hM hB hv (moment_bound M n r y A hA hy) μ ⟨p2,hdμ.2⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),frame r3 hdμ (by decide) (by decide),p3⟩

def vector : Com := .seq (.assign "lp.position" (.lit 0))
  (RamVectorEncoding.command "conditioning.v" "graph.n" read)

theorem vector_spec (B M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n))
    (hM : 1≤M) (hA : A.card≤r) (hN : 3*N n r+10<B) (hn : 3*n+3<B) (hm : 2^n<B)
    (hB : 2*M^2+3<B) (hy : ∀ T,Bounded M (y T)) :
    Spec B (fun σ => Data y A σ ∧ 3*n<(σ.arrs "lp.word").length) vector
      (fun _ τ => Data y A τ ∧ Prefix (encodeVector (values y A)) "lp.word" τ ∧ τ.vars "lp.position"=3*n)
      ((17*N n r+72*(M^2).size+222)*n+8) := by
  have hMB : M^2<B := by nlinarith
  have hh := RamVectorEncoding.command_spec B (17*N n r+72*(M^2).size+187) (Data y A)
    "conditioning.v" "graph.n" (List.ofFn (values y A)) [] read (by omega)
    (by simp; omega)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (height M n r y A hM hA hy ⟨i,by simpa using hi⟩).1.trans_lt hMB)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (height M n r y A hM hA hy ⟨i,by simpa using hi⟩).2.trans_lt hMB)
    (fun σ h => by simpa only [List.length_ofFn] using h.1.2.2)
    (fun σ k h => by simpa only [Data,NativeConditioningVector.Data,NativeMomentValue.Context,
      Prefix,Stored,String.reduceAppend,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (by intro i hi; simpa only [List.getElem_ofFn] using read_spec B M n r y A ⟨i,by simpa using hi⟩ hM hA hN (by omega) hm hB hy)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide)) (by decide)
  rintro σ ⟨hd,hr⟩
  have r1 : Run B (.assign "lp.position" (.lit 0)) σ (σ.setVar "lp.position" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨τ,r2,p2⟩ := hh (σ.setVar "lp.position" 0)
    ⟨frame r1 hd (by decide) (by decide),by simp [Prefix],by simp,
      by simpa only [List.length_nil,List.length_ofFn,arrs_setVar,Nat.zero_add] using hr⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [List.length_ofFn,Nat.add_assoc,Nat.reduceAdd]; omega),p2.1,?_,?_⟩
  · simpa only [List.nil_append,RamVectorEncoding.encode,encodeVector] using p2.2.1
  · simpa only [List.length_nil,List.length_ofFn,Nat.zero_add] using p2.2.2

def prepare : Com := .seq (.assign "lookup.key" (.var "conditioning.mask"))
  (.seq NativeMomentValue.command (save "quotient.denominator"))

theorem prepare_spec (B M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n))
    (hA : A.card≤r) (hN : 3*N n r+10<B) (hm : 2^n<B) (hM : M<B)
    (hy : ∀ T,Bounded M (y T)) :
    Spec B (NativeConditioningVector.Data y A) prepare (fun _ τ => Data y A τ) (17*N n r+39) := by
  intro σ hd
  let ν := σ.setVar "lookup.key" (NativeMasks.mask A)
  have r1 : Run B (.assign "lookup.key" (.var "conditioning.mask")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hd.2.1.symm,hd.2.1 ▸ (NativeMasks.mask_bound A).trans hm⟩)
  have hdν := NativeConditioningVector.frame r1 hd (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨μ,r2,p2⟩ := NativeMomentValue.command_spec B M n r y A (by omega) hN hm hM hy ν ⟨hdν.1,by simp [ν]⟩
  have hq := moment_bound M n r y A hA hy
  obtain ⟨τ,r3,p3⟩ := save_spec B "quotient.denominator" (rationalValue y A) (by omega)
    (hq.1.trans_lt hM) (hq.2.trans_lt hM) (by decide) μ p2.2
  have rr := r1.seq (r2.seq r3)
  exact ⟨τ,rr.mono (by omega),NativeConditioningVector.frame rr hd (by decide) (by decide) (by decide) (by decide) (by decide),p3⟩

def copySetup : Com := .seq (.assign "slice.start" (.lit 0)) (.assign "fill.length" (.mul (.lit 3) (.var "graph.n")))

def command : Com := .seq prepare (.seq vector (.seq copySetup (NativeSlice.command "lp.word" "near.costs")))

theorem command_spec (B M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n))
    (hM : 1≤M) (hA : A.card≤r) (hN : 3*N n r+10<B) (hn : 3*n+3<B) (hm : 2^n<B)
    (hB : 2*M^2+3<B) (hy : ∀ T,Bounded M (y T)) :
    Spec B (fun σ => NativeConditioningVector.Data y A σ ∧ 3*n<(σ.arrs "lp.word").length ∧
      3*n≤(σ.arrs "near.costs").length) command
      (fun _ τ => Data y A τ ∧ Prefix (encodeVector (values y A)) "near.costs" τ)
      ((17*N n r+72*(M^2).size+270)*n+17*N n r+59) := by
  have hlen : (encodeVector (values y A)).length=3*n := by
    change (RamVectorEncoding.encode (List.ofFn (values y A))).length=_
    rw [RamVectorEncoding.length_encode,List.length_ofFn]
  have hsetup : Spec B (fun σ => σ.vars "graph.n"=n) copySetup
      (fun _ τ => τ.vars "slice.start"=0 ∧ τ.vars "fill.length"=3*n) 6 := by
    run_vcg
    all_goals simp_all
  rintro σ ⟨hd,hO,hC⟩
  obtain ⟨ν,r1,p1⟩ := prepare_spec B M n r y A hA hN hm (by nlinarith) hy σ hd
  obtain ⟨μ,r2,p2⟩ := vector_spec B M n r y A hM hA hN hn hm hB hy ν
    ⟨p1,by rwa [RamFrames.run_array_length r1]⟩
  obtain ⟨ξ,r3,p3⟩ := hsetup μ p2.1.1.2.2
  have hp : Prefix (encodeVector (values y A)) "lp.word" ξ := by
    simpa only [Prefix,r3.frame_arr "lp.word" (by decide)] using p2.2.1
  obtain ⟨τ,r4,p4⟩ := NativeSlice.command_spec B "lp.word" "near.costs" [] (encodeVector (values y A)) []
    (by decide) (by rw [List.length_nil,hlen]; omega)
    (NativeRationalBounds.vector_words B (M^2) n (values y A) (by omega) (by nlinarith) (height M n r y A hM hA hy)) ξ
    ⟨⟨by simpa using hp,by simpa using p3.1⟩,by simpa only [hlen] using p3.2,
      by rw [hlen,RamFrames.run_array_length (r1.seq (r2.seq r3))]; exact hC⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by rw [hlen]; nlinarith),
    frame (r3.seq r4) p2.1 (by decide) (by decide),p4.2⟩

end Lax263307Proofs.NativeNearCosts
