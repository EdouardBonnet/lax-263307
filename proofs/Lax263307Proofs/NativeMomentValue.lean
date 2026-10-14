import Lax263307Proofs.NativeWordLookup
import Lax263307Proofs.NativeMomentAccess
import Lax263307Proofs.NativeRationalBounds

namespace Lax263307Proofs.NativeMomentValue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalEncoding
open Lax263307 RationalConditioning NativeSignedArithmetic
open NativeCatalogMetadata

def keys (n r : ℕ) (i : Fin (N n r)) : ℕ := NativeMasks.mask (atIndex n r i)

def values {n r : ℕ} (y : RationalVector n r) (i : Fin (N n r)) : ℚ :=
  y (CoordinateCatalog.indexing n r i)

theorem values_decode {n r : ℕ} (x : Fin (N n r) → ℚ) : values (MomentLP.decode x)=x := by
  funext i
  simp only [values,MomentLP.decode,Equiv.symm_apply_apply]

def Context {n r : ℕ} (y : RationalVector n r) (σ : Env) : Prop :=
  Prefix (Lax263307.NativeCatalog.words n r) "catalog.mask" σ ∧
  Prefix (encodeVector (values y)) "near.moments" σ ∧ σ.vars "catalog.count"=N n r

theorem keys_injective (n r : ℕ) : Function.Injective (keys n r) := by
  intro i j h
  apply (CoordinateCatalog.indexing n r).injective
  exact Subtype.ext (NativeMasks.mask_injective n h)

theorem keys_words (n r : ℕ) : List.ofFn (keys n r)=Lax263307.NativeCatalog.words n r := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_ofFn]
  by_cases hj : j<N n r
  · rw [dif_pos hj,NativeMomentAccess.mask_word n r ⟨j,hj⟩]
    rfl
  · rw [dif_neg hj,List.getElem?_eq_none]
    simpa only [Lax263307.NativeCatalog.words,List.length_map] using Nat.le_of_not_gt hj

def command : Com := .seq (.assign "lookup.count" (.var "catalog.count"))
  (.seq (NativeWordLookup.command "catalog.mask")
    (.seq (.assign "read.cursor" (.mul (.lit 3) (.var "lookup.result")))
      (NativeRationalRead.command "near.moments")))

/-- Read the requested moment from its actual catalog position. The
search uses O(N) source instructions and O(N) stored words, even when
the subset mask has a large numerical value. -/
theorem command_spec (B M n r : ℕ) (y : RationalVector n r) (A : Finset (Fin n))
    (hA : A.card≤r+2) (hN : 3*N n r+10<B) (hm : 2^n<B) (hM : M<B)
    (hy : ∀ T,Bounded M (y T)) :
    Spec B (fun σ => Context y σ ∧ σ.vars "lookup.key"=NativeMasks.mask A) command
      (fun _ τ => Context y τ ∧ RamRational.FractionOutput (rationalValue y A) τ)
      (17*N n r+31) := by
  let i := (CoordinateCatalog.indexing n r).symm ⟨A,hA⟩
  have hiA : atIndex n r i=A := congrArg Subtype.val ((CoordinateCatalog.indexing n r).apply_symm_apply ⟨A,hA⟩)
  have hiY : values y i=rationalValue y A := by simp [values,i,rationalValue,hA]
  rintro σ ⟨hc,hkey⟩
  let ν := σ.setVar "lookup.count" (N n r)
  have r1 : Run B (.assign "lookup.count" (.var "catalog.count")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hc.2.2.symm,hc.2.2 ▸ (by omega : N n r<B)⟩)
  obtain ⟨μ,r2,p2⟩ := NativeWordLookup.command_spec B (N n r) "catalog.mask" (keys n r)
    (keys_injective n r) (fun j => (NativeMasks.mask_bound _).trans hm) (by omega) i ν
    ⟨by simpa only [keys_words,Prefix,ν,arrs_setVar] using hc.1,
      by simp [ν],by simpa only [keys,hiA,ν,vars_setVar,String.reduceEq,if_false] using hkey⟩
  let ξ := μ.setVar "read.cursor" (3*i.val)
  have r3 : Run B (.assign "read.cursor" (.mul (.lit 3) (.var "lookup.result"))) μ ξ 4 :=
    Run.assign (evalB_bin (op := .mul) (evalB_lit (by omega : 3<B))
      (by rw [evalB_var_iff]; exact ⟨p2.2.symm,p2.2 ▸ (by have hh := i.isLt; omega : i.val<B)⟩)
      (by change 3*i.val<B; have hh := i.isLt; omega))
  have hsource : Prefix (encodeVector (values y)) "near.moments" ξ := by
    simpa only [Prefix,(r1.seq (r2.seq r3)).frame_arr "near.moments" (by decide)] using hc.2.1
  obtain ⟨τ,r4,p4⟩ := NativeRationalRead.vector_entry_spec B "near.moments" [] [] (List.ofFn (values y))
    i.val (by simpa using i.isLt) (by omega) (by simp; have hh := i.isLt; omega)
    (by simpa only [List.getElem_ofFn,values] using (hy (CoordinateCatalog.indexing n r i)).1.trans_lt hM)
    (by simpa only [List.getElem_ofFn,values] using (hy (CoordinateCatalog.indexing n r i)).2.trans_lt hM) ξ
    ⟨by simpa only [List.nil_append,List.append_nil,NativeRationalTabulate.words,encodeVector] using hsource,
      by simp [ξ]⟩
  have rr := r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rr.mono (by omega),?_,by simpa only [List.getElem_ofFn,hiY] using p4.1⟩
  simpa only [Context,Prefix,rr.frame_arr "catalog.mask" (by decide),
    rr.frame_arr "near.moments" (by decide),rr.frame_var "catalog.count" (by decide)] using hc

end Lax263307Proofs.NativeMomentValue
