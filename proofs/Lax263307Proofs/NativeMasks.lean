import Lax263307.IndependentSetEncoding
import Lax263307Proofs.NativeCombinations
import Lax263307.NativeCatalog
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMasks

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

/-- A coordinate is stored in one word; bit positions are original vertex labels. -/
abbrev mask {n : ℕ} (I : Finset (Fin n)) : ℕ :=
  Lax263307.NativeCatalog.subsetMask I

theorem mask_test_bit {n : ℕ} (I : Finset (Fin n)) (j : ℕ) :
    (mask I).testBit j=decide (j∈I.image Fin.val) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff,←Nat.mem_bitIndices,←List.mem_toFinset]
  change j∈Finset.equivBitIndices (mask I) ↔ j∈I.image Fin.val
  rw [mask,Lax263307.NativeCatalog.subsetMask,Equiv.apply_symm_apply]

theorem mask_member {n : ℕ} (I : Finset (Fin n)) (v : Fin n) :
    (mask I).testBit v.val=decide (v∈I) := by
  rw [mask_test_bit]
  congr 1
  simp [Finset.mem_image,Fin.val_inj]

theorem mask_injective (n : ℕ) : Function.Injective (mask (n:=n)) := by
  intro I J h
  ext v
  have hh := congrArg (fun m : ℕ => m.testBit v.val) h
  simpa only [mask_member,decide_eq_decide] using hh

theorem mask_empty (n : ℕ) : mask (∅ : Finset (Fin n))=0 := by
  simp [mask,Lax263307.NativeCatalog.subsetMask,Finset.equivBitIndices]

theorem mask_bound {n : ℕ} (I : Finset (Fin n)) : mask I<2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [mask_test_bit]
  apply decide_eq_false_iff_not.mpr
  intro hjm
  obtain ⟨v,hv,hvj⟩ := Finset.mem_image.mp hjm
  have hvn := v.isLt
  omega

theorem mask_insert {n : ℕ} (I : Finset (Fin n)) (v : Fin n) :
    mask (insert v I)=Nat.lor (mask I) (2^v.val) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (insert v I)).testBit j = ((mask I) ||| (2^v.val)).testBit j
  rw [Nat.testBit_or,mask_test_bit,mask_test_bit,Nat.testBit_two_pow]
  simp only [Finset.image_insert,Finset.mem_insert]
  by_cases he : j=v.val <;> by_cases hm : j∈I.image Fin.val <;> simp [he,hm,eq_comm]

def initialSet {n : ℕ} (I : Finset (Fin n)) (i : ℕ) : Finset (Fin n) :=
  I.filter fun v => v.val < i

theorem prefix_zero {n : ℕ} (I : Finset (Fin n)) : initialSet I 0=∅ := by simp [initialSet]

theorem prefix_full {n : ℕ} (I : Finset (Fin n)) : initialSet I n=I := by simp [initialSet]

theorem prefix_succ {n : ℕ} (I : Finset (Fin n)) (i : ℕ) (hi : i<n) :
    initialSet I (i+1)=if (⟨i,hi⟩ : Fin n)∈I then insert ⟨i,hi⟩ (initialSet I i) else initialSet I i := by
  ext v
  by_cases hv : v.val=i
  · have he : v=⟨i,hi⟩ := Fin.ext hv
    subst v
    by_cases hm : (⟨i,hi⟩ : Fin n)∈I <;> simp [initialSet,hm]
  · have he : v≠⟨i,hi⟩ := fun h => hv (congrArg Fin.val h)
    by_cases hm : (⟨i,hi⟩ : Fin n)∈I <;> simp [hm,initialSet,he] <;> omega

theorem prefix_step {n : ℕ} (I : Finset (Fin n)) (i : ℕ) (hi : i<n) :
    Nat.lor (mask (initialSet I i)) ((if (⟨i,hi⟩ : Fin n)∈I then 1 else 0)*2^i)=mask (initialSet I (i+1)) := by
  rw [prefix_succ I i hi]
  by_cases h : (⟨i,hi⟩ : Fin n)∈I
  · simp only [if_pos h,one_mul,mask_insert]
  · simp [h]

def step : Com := .seq (.assign "mask.value"
  (.or (.var "mask.value") (.shiftl (.get "subset.bits" (.var "mask.i")) (.var "mask.i"))))
  (.assign "mask.i" (.add (.var "mask.i") (.lit 1)))

def Invariant {n : ℕ} (I : Finset (Fin n)) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "mask.i"≤n ∧
  Prefix (encodeOutput I) "subset.bits" σ ∧ σ.vars "mask.value"=mask (initialSet I (σ.vars "mask.i"))

theorem step_spec {n : ℕ} (B : ℕ) (I : Finset (Fin n)) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => Invariant I σ ∧ σ.vars "mask.i"<n) step
      (fun σ τ => Invariant I τ ∧ τ.vars "mask.i"=σ.vars "mask.i"+1) 11 := by
  rintro σ ⟨⟨hn,hle,hbits,hmask⟩,hlt⟩
  let i := σ.vars "mask.i"
  let bit := if (⟨i,hlt⟩ : Fin n)∈I then 1 else 0
  have hbit : bit≤1 := by dsimp [bit]; split_ifs <;> omega
  have hbitB : bit<B := by omega
  have hiB : i<B := by omega
  have hpow : 2^i<2^n := Nat.pow_lt_pow_right (by omega) hlt
  have hshift : bit*2^i<B := (by simpa only [one_mul] using Nat.mul_le_mul_right (2^i) hbit : bit*2^i≤2^i).trans_lt (hpow.trans hm)
  have hget : (σ.arrs "subset.bits")[i]?=some bit := by
    have hh := hbits i (by simpa [encodeOutput] using hlt)
    simpa [encodeOutput,bit] using hh
  have hprev : mask (initialSet I i)<B := (mask_bound _).trans hm
  have hnext : mask (initialSet I (i+1))<B := (mask_bound _).trans hm
  have hval : (Expr.or (.var "mask.value") (.shiftl (.get "subset.bits" (.var "mask.i")) (.var "mask.i"))).evalB B σ=
      some (mask (initialSet I (i+1))) := by
    have hh := evalB_bin (op := .or)
      (by rw [evalB_var_iff]; exact ⟨hmask.symm,hmask ▸ hprev⟩)
      (evalB_bin (op := .shiftl) (evalB_get (evalB_var hiB) hget hbitB) (evalB_var hiB) hshift)
      (by change Nat.lor (mask (initialSet I i)) (bit*2^i)<B; rw [prefix_step]; exact hnext)
    simpa only [Bop.apply_or,Bop.apply_shiftl,←show σ.vars "mask.i"=i from rfl,bit,prefix_step] using hh
  let ν := σ.setVar "mask.value" (mask (initialSet I (i+1)))
  have r1 : Run B (.assign "mask.value"
      (.or (.var "mask.value") (.shiftl (.get "subset.bits" (.var "mask.i")) (.var "mask.i")))) σ ν 7 :=
    Run.assign hval
  have hiν : ν.vars "mask.i"=i := by simp [ν,i]
  let τ := ν.setVar "mask.i" (i+1)
  have r2 : Run B (.assign "mask.i" (.add (.var "mask.i") (.lit 1))) ν τ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩) (evalB_lit (by omega))
      (by change i+1<B; omega))
  have rr := r1.seq r2
  have ht : τ.vars "mask.i"=i+1 := by simp [τ]
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by decide)).trans hn,by rw [ht]; omega,?_,?_⟩,ht⟩
  · simpa only [Prefix,rr.frame_arr "subset.bits" (by decide)] using hbits
  · simp [τ,ν]

def command : Com := .seq (.assign "mask.value" (.lit 0))
  (.seq (.assign "mask.i" (.lit 0)) (.while (.lt (.var "mask.i") (.var "graph.n")) step))

theorem command_spec {n : ℕ} (B : ℕ) (I : Finset (Fin n)) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ Prefix (encodeOutput I) "subset.bits" σ) command
      (fun _ τ => τ.vars "mask.value"=mask I) (15*n+8) := by
  have hloop := Spec.forRangeZero "mask.i" "graph.n" (Invariant I) n 11 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (step_spec B I hB hm)
  rintro σ ⟨hn,hbits⟩
  let ν := σ.setVar "mask.value" 0
  have r1 : Run B (.assign "mask.value" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hi : Invariant I (ν.setVar "mask.i" 0) := by
    refine ⟨?_,by simp,hbits,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simp [ν,prefix_zero,mask_empty]
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by omega),?_⟩
  simpa only [p2.2,prefix_full] using p2.1.2.2.2

end Lax263307Proofs.NativeMasks
