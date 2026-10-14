import Lax263307Proofs.NativeMomentValue
import Lax455465Proofs.RamVectorEncoding

namespace Lax263307Proofs.NativeConditioningVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic
open NativeCatalogMetadata

def Data {n r : ℕ} (y : RationalVector n r) (A : Finset (Fin n)) (σ : Env) : Prop :=
  NativeMomentValue.Context y σ ∧ σ.vars "conditioning.mask"=NativeMasks.mask A ∧ σ.vars "graph.n"=n

theorem frame {B n r K : ℕ} {y : RationalVector n r} {A : Finset (Fin n)}
    {c : Com} {σ τ : Env} (rr : Run B c σ τ K) (hd : Data y A σ)
    (h0 : "catalog.mask"∉c.warrs) (h1 : "near.moments"∉c.warrs)
    (h2 : "catalog.count"∉c.wvars) (h3 : "conditioning.mask"∉c.wvars)
    (h4 : "graph.n"∉c.wvars) : Data y A τ := by
  simpa only [Data,NativeMomentValue.Context,Prefix,rr.frame_arr "catalog.mask" h0,
    rr.frame_arr "near.moments" h1,rr.frame_var "catalog.count" h2,
    rr.frame_var "conditioning.mask" h3,rr.frame_var "graph.n" h4] using hd

def key : Com := .assign "lookup.key"
  (.or (.var "conditioning.mask") (.shiftl (.lit 1) (.var "conditioning.v")))

def read : Com := .seq key NativeMomentValue.command

def command : Com := .seq (.assign "lp.position" (.lit 0))
  (RamVectorEncoding.command "conditioning.v" "graph.n" read)

theorem key_spec (B n : ℕ) (A : Finset (Fin n)) (v : Fin n)
    (hn : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "conditioning.mask"=NativeMasks.mask A ∧
      σ.vars "conditioning.v"=v.val) key
      (fun _ τ => τ.vars "lookup.key"=NativeMasks.mask (insert v A)) 6 := by
  rintro σ ⟨hA,hv⟩
  have hpow : 2^v.val<B := (Nat.pow_lt_pow_right (by decide) v.isLt).trans hm
  have he : (Expr.or (.var "conditioning.mask") (.shiftl (.lit 1) (.var "conditioning.v"))).evalB B σ=
      some (NativeMasks.mask (insert v A)) := by
    have hh := evalB_bin (op := .or)
      (by rw [evalB_var_iff]; exact ⟨hA.symm,hA ▸ (NativeMasks.mask_bound _).trans hm⟩)
      (evalB_bin (op := .shiftl) (evalB_lit (by omega : 1<B))
        (by rw [evalB_var_iff]; exact ⟨hv.symm,hv ▸ (by have hh := v.isLt; omega : v.val<B)⟩)
        (by simpa only [Bop.apply_shiftl,one_mul] using hpow))
      (by simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,←NativeMasks.mask_insert]
        using (NativeMasks.mask_bound (insert v A)).trans hm)
    simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,←NativeMasks.mask_insert] using hh
  exact ⟨σ.setVar "lookup.key" (NativeMasks.mask (insert v A)),Run.assign he,by simp⟩

theorem read_spec (B M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n)) (v : Fin n)
    (hA : A.card≤r) (hN : 3*N n r+10<B) (hn : n+2<B) (hm : 2^n<B) (hM : M<B)
    (hy : ∀ T,Bounded M (y T)) :
    Spec B (fun σ => Data y A σ ∧ σ.vars "conditioning.v"=v.val) read
      (fun _ τ => Data y A τ ∧ RamRational.FractionOutput (rationalValue y (insert v A)) τ)
      (17*N n r+37) := by
  rintro σ ⟨hd,hv⟩
  obtain ⟨ν,r1,p1⟩ := key_spec B n A v hn hm σ ⟨hd.2.1,hv⟩
  have hdν := frame r1 hd (by decide) (by decide) (by decide) (by decide) (by decide)
  have hiA : (insert v A).card≤r+2 := (Finset.card_insert_le v A).trans (by omega)
  obtain ⟨τ,r2,p2⟩ := NativeMomentValue.command_spec B M n r y (insert v A) hiA hN hm hM hy ν ⟨hdν.1,p1⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),
    frame r2 hdν (by decide) (by decide) (by decide) (by decide) (by decide),p2.2⟩

/-- Materialize the exact moments y(A ∪ {v}) in vertex order. All moment
coordinates are read from the previously stored near projection point. -/
theorem command_spec (B M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n))
    (hA : A.card≤r) (hN : 3*N n r+10<B) (hn : 3*n+3<B) (hm : 2^n<B) (hM : M<B)
    (hy : ∀ T,Bounded M (y T)) :
    Spec B (fun σ => Data y A σ ∧ 3*n<(σ.arrs "lp.word").length) command
      (fun _ τ => Data y A τ ∧ Prefix (encodeVector (fun v => rationalValue y (insert v A))) "lp.word" τ ∧
        τ.vars "lp.position"=3*n) ((17*N n r+72)*n+8) := by
  have hv (v : Fin n) : Bounded M (rationalValue y (insert v A)) := by
    have hh : (insert v A).card≤r+2 := (Finset.card_insert_le v A).trans (by omega)
    simpa only [rationalValue,dif_pos hh] using hy ⟨insert v A,hh⟩
  have hh := RamVectorEncoding.command_spec B (17*N n r+37) (Data y A)
    "conditioning.v" "graph.n" (List.ofFn (fun v => rationalValue y (insert v A))) [] read (by omega)
    (by simp; omega)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hv ⟨i,by simpa using hi⟩).1.trans_lt hM)
    (by intro i hi; simp only [List.getElem_ofFn]; exact (hv ⟨i,by simpa using hi⟩).2.trans_lt hM)
    (fun σ h => by simpa only [List.length_ofFn] using h.2.2)
    (fun σ k h => by simpa only [Data,NativeMomentValue.Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (by intro i hi; simpa only [List.getElem_ofFn] using read_spec B M n r y A ⟨i,by simpa using hi⟩ hA hN (by omega) hm hM hy)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame rr h (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)
  rintro σ ⟨hd,hr⟩
  have r1 : Run B (.assign "lp.position" (.lit 0)) σ (σ.setVar "lp.position" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨τ,r2,p2⟩ := hh (σ.setVar "lp.position" 0)
    ⟨frame r1 hd (by decide) (by decide) (by decide) (by decide) (by decide),
      by simp [Prefix],by simp,by simpa only [List.length_nil,List.length_ofFn,arrs_setVar,Nat.zero_add] using hr⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [List.length_ofFn,Nat.add_assoc,Nat.reduceAdd]; omega),p2.1,?_,?_⟩
  · simpa only [List.nil_append,RamVectorEncoding.encode,encodeVector] using p2.2.1
  · simpa only [List.length_nil,List.length_ofFn,Nat.zero_add] using p2.2.2

end Lax263307Proofs.NativeConditioningVector
