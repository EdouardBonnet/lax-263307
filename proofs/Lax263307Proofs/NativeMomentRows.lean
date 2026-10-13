import Lax263307Proofs.NativeMasks
import Lax263307.MomentLP

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks
open Lax263307

def same {n : ℕ} (A J : Finset (Fin n)) : ℕ := if A=J then 1 else 0

theorem same_le {n : ℕ} (A J : Finset (Fin n)) : same A J≤1 := by unfold same; split_ifs <;> omega

theorem same_masks {n : ℕ} (A J : Finset (Fin n)) :
    (if mask A=mask J then 1 else 0)=same A J := by simp only [(mask_injective n).eq_iff,same]

theorem same_single_row {n r : ℕ} (A : Finset (Fin n)) (j : MomentLP.Index n r) :
    (same A (CoordinateCatalog.indexing n r j).val : ℚ)=MomentLP.singleRow A j := by
  simp only [same,MomentLP.singleRow,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

def compare (dst left right : String) : Com :=
  .ite (.eq (.var left) (.var right)) (.assign dst (.lit 1)) (.assign dst (.lit 0))

theorem compare_spec (B a b : ℕ) (dst left right : String) (ha : a<B) (hb : b<B) (h1 : 1<B) :
    Spec B (fun σ => σ.vars left=a ∧ σ.vars right=b) (compare dst left right)
      (fun _ τ => τ.vars dst=if a=b then 1 else 0) 6 := by
  rintro σ ⟨hleft,hright⟩
  have hcond := evalB_condEq
    (by rw [evalB_var_iff]; exact ⟨hleft.symm,hleft ▸ ha⟩)
    (by rw [evalB_var_iff]; exact ⟨hright.symm,hright ▸ hb⟩)
  by_cases h : a=b
  · have hc : (Cond.eq (.var left) (.var right)).evalB B σ=some true := by simpa only [h,beq_self_eq_true] using hcond
    have hr := Run.ite_true (d := .assign dst (.lit 0)) hc (Run.assign (x:=dst) (evalB_lit h1))
    exact ⟨_,hr,by simp [h]⟩
  · have hc : (Cond.eq (.var left) (.var right)).evalB B σ=some false := by simpa only [beq_eq_false_iff_ne.mpr h] using hcond
    have hr := Run.ite_false (c := .assign dst (.lit 1)) hc (Run.assign (x:=dst) (evalB_lit (by omega : 0<B)))
    exact ⟨_,hr,by simp [h]⟩

def insertCommand : Com := .assign "row.insert" (.or (.var "row.mask") (.shiftl (.lit 1) (.var "row.v")))

theorem insert_spec {n : ℕ} (B : ℕ) (A : Finset (Fin n)) (v : Fin n) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "row.mask"=mask A ∧ σ.vars "row.v"=v.val) insertCommand
      (fun _ τ => τ.vars "row.insert"=mask (insert v A)) 6 := by
  rintro σ ⟨hA,hv⟩
  have hAv : mask A<B := (mask_bound _).trans hm
  have hvB : v.val<B := v.isLt.trans (by omega)
  have hpow : 2^v.val<B := (Nat.pow_lt_pow_right (by omega) v.isLt).trans hm
  have hins : mask (insert v A)<B := (mask_bound _).trans hm
  have hval : (Expr.or (.var "row.mask") (.shiftl (.lit 1) (.var "row.v"))).evalB B σ=some (mask (insert v A)) := by
    have hh := evalB_bin (op := .or)
      (by rw [evalB_var_iff]; exact ⟨hA.symm,hA ▸ hAv⟩)
      (evalB_bin (op := .shiftl) (evalB_lit (show 1<B by omega))
        (by rw [evalB_var_iff]; exact ⟨hv.symm,hv ▸ hvB⟩) (by simpa only [Bop.apply_shiftl,one_mul] using hpow))
      (by change Nat.lor (mask A) (1*2^v.val)<B; simpa only [one_mul,←mask_insert] using hins)
    simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,←mask_insert] using hh
  exact ⟨_,Run.assign hval,by simp⟩

def monotoneCommand : Com := .seq insertCommand
  (.seq (compare "coefficient.positive" "row.insert" "column.mask")
    (compare "coefficient.negative" "row.mask" "column.mask"))

theorem monotone_spec {n : ℕ} (B : ℕ) (A J : Finset (Fin n)) (v : Fin n) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "row.mask"=mask A ∧ σ.vars "column.mask"=mask J ∧ σ.vars "row.v"=v.val)
      monotoneCommand (fun _ τ => τ.vars "coefficient.positive"=same (insert v A) J ∧ τ.vars "coefficient.negative"=same A J) 18 := by
  rintro σ ⟨hA,hJ,hv⟩
  obtain ⟨ν,r1,p1⟩ := insert_spec B A v hB hm σ ⟨hA,hv⟩
  obtain ⟨μ,r2,p2⟩ := compare_spec B (mask (insert v A)) (mask J) "coefficient.positive" "row.insert" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) (by omega) ν
    ⟨p1,(r1.frame_var "column.mask" (by decide)).trans hJ⟩
  have r12 := r1.seq r2
  obtain ⟨τ,r3,p3⟩ := compare_spec B (mask A) (mask J) "coefficient.negative" "row.mask" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) (by omega) μ
    ⟨(r12.frame_var "row.mask" (by decide)).trans hA,(r12.frame_var "column.mask" (by decide)).trans hJ⟩
  refine ⟨τ,r1.seq (r2.seq r3),?_,?_⟩
  · rw [r3.frame_var "coefficient.positive" (by decide),p2,same_masks]
  · simpa only [same_masks] using p3

theorem monotone_value {n r : ℕ} (A : Finset (Fin n)) (v : Fin n) (j : MomentLP.Index n r) :
    (same (insert v A) (CoordinateCatalog.indexing n r j).val : ℚ)-same A (CoordinateCatalog.indexing n r j).val=
      MomentLP.monotoneRow A v j := by rw [same_single_row,same_single_row]; rfl

def matchCount {n : ℕ} (A J : Finset (Fin n)) (i : ℕ) : ℕ :=
  ((List.finRange n).take i).countP fun v => decide (insert v A=J)

theorem matches_zero {n : ℕ} (A J : Finset (Fin n)) : matchCount A J 0=0 := by simp [matchCount]

theorem matches_bound {n : ℕ} (A J : Finset (Fin n)) (i : ℕ) : matchCount A J i≤n := by
  have h : matchCount A J i≤((List.finRange n).take i).length := List.countP_le_length
  simp only [List.length_take,List.length_finRange] at h
  omega

theorem matches_succ {n : ℕ} (A J : Finset (Fin n)) (i : ℕ) (hi : i<n) :
    matchCount A J (i+1)=matchCount A J i+same (insert ⟨i,hi⟩ A) J := by
  have hilen : i<(List.finRange n).length := by simpa using hi
  simp only [matchCount,List.take_succ_eq_append_getElem hilen,List.countP_append,List.countP_singleton,
    List.getElem_finRange,same,decide_eq_true_eq]
  rfl

theorem countP_as_sum {α : Type*} (xs : List α) (f : α → Bool) :
    xs.countP f=(xs.map fun x => if f x then 1 else 0).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases h : f a <;> simp [h,ih,Nat.add_comm]

theorem matches_value {n r : ℕ} (A : Finset (Fin n)) (j : MomentLP.Index n r) :
    (matchCount A (CoordinateCatalog.indexing n r j).val n : ℚ)=∑ v, MomentLP.singleRow (insert v A) j := by
  rw [matchCount,List.take_of_length_le (by simp),countP_as_sum,←List.ofFn_eq_map,List.sum_ofFn]
  simp [MomentLP.singleRow]

theorem mass_value {n r : ℕ} (A : Finset (Fin n)) (k : ℕ) (j : MomentLP.Index n r) :
    (matchCount A (CoordinateCatalog.indexing n r j).val n : ℚ)-(k*same A (CoordinateCatalog.indexing n r j).val : ℕ)=
      MomentLP.massRow A k j := by
  rw [matches_value,Nat.cast_mul,same_single_row]
  rfl

def countBranch : Com := .ite (.eq (.var "row.insert") (.var "column.mask"))
  (.assign "coefficient.positive" (.add (.var "coefficient.positive") (.lit 1))) .skip

def countStep : Com := .seq insertCommand (.seq countBranch (.assign "row.v" (.add (.var "row.v") (.lit 1))))

def CountInvariant {n : ℕ} (A J : Finset (Fin n)) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "row.mask"=mask A ∧ σ.vars "column.mask"=mask J ∧
  σ.vars "row.v"≤n ∧ σ.vars "coefficient.positive"=matchCount A J (σ.vars "row.v")

theorem count_step_spec {n : ℕ} (B : ℕ) (A J : Finset (Fin n)) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => CountInvariant A J σ ∧ σ.vars "row.v"<n) countStep
      (fun σ τ => CountInvariant A J τ ∧ τ.vars "row.v"=σ.vars "row.v"+1) 18 := by
  rintro σ ⟨⟨hn,hA,hJ,hle,hcount⟩,hlt⟩
  let i := σ.vars "row.v"
  let v : Fin n := ⟨i,hlt⟩
  have hiB : i<B := by omega
  obtain ⟨ν,r1,p1⟩ := insert_spec B A v hB hm σ ⟨hA,rfl⟩
  have hcolν : ν.vars "column.mask"=mask J := (r1.frame_var "column.mask" (by decide)).trans hJ
  have hcountν : ν.vars "coefficient.positive"=matchCount A J i :=
    (r1.frame_var "coefficient.positive" (by decide)).trans hcount
  have hcB : matchCount A J i<B := (matches_bound A J i).trans_lt (by omega)
  have hc1B : matchCount A J i+1<B := by have h := matches_bound A J i; omega
  have heval := evalB_condEq
    (by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ (mask_bound _).trans hm⟩)
    (by rw [evalB_var_iff]; exact ⟨hcolν.symm,hcolν ▸ (mask_bound _).trans hm⟩)
  obtain ⟨μ,r2,p2⟩ : ∃ μ,Run B countBranch ν μ 8 ∧ μ.vars "coefficient.positive"=matchCount A J (i+1) := by
    by_cases h : insert v A=J
    · have he : mask (insert v A)=mask J := congrArg mask h
      have hb : (Cond.eq (.var "row.insert") (.var "column.mask")).evalB B ν=some true := by
        simpa only [he,beq_self_eq_true] using heval
      have hv : (Expr.add (.var "coefficient.positive") (.lit 1)).evalB B ν=some (matchCount A J i+1) :=
        evalB_bin (op := .add)
          (by rw [evalB_var_iff]; exact ⟨hcountν.symm,hcountν ▸ hcB⟩) (evalB_lit (by omega)) hc1B
      refine ⟨_,Run.ite_true (d := .skip) hb (Run.assign hv),?_⟩
      simp only [vars_setVar,if_true,matches_succ A J i hlt,same,show insert ⟨i,hlt⟩ A=J from h,if_true]
    · have he : mask (insert v A)≠mask J := fun he => h ((mask_injective n) he)
      have hb : (Cond.eq (.var "row.insert") (.var "column.mask")).evalB B ν=some false := by
        simpa only [beq_eq_false_iff_ne.mpr he] using heval
      refine ⟨ν,(Run.ite_false (c := .assign "coefficient.positive" (.add (.var "coefficient.positive") (.lit 1))) hb Run.skip).mono (by decide),?_⟩
      simpa only [matches_succ A J i hlt,same,show ¬insert ⟨i,hlt⟩ A=J from h,if_false,Nat.add_zero] using hcountν
  have r12 := r1.seq r2
  have hiμ : μ.vars "row.v"=i := r12.frame_var "row.v" (by decide)
  let τ := μ.setVar "row.v" (i+1)
  have r3 : Run B (.assign "row.v" (.add (.var "row.v") (.lit 1))) μ τ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩) (evalB_lit (by omega)) (by change i+1<B; omega))
  have rr := r1.seq (r2.seq r3)
  have ht : τ.vars "row.v"=i+1 := by simp [τ]
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by decide)).trans hn,
    (rr.frame_var "row.mask" (by decide)).trans hA,(rr.frame_var "column.mask" (by decide)).trans hJ,
    by rw [ht]; omega,?_⟩,ht⟩
  rw [ht,r3.frame_var "coefficient.positive" (by decide)]
  exact p2

def countCommand : Com := .seq (.assign "coefficient.positive" (.lit 0))
  (.seq (.assign "row.v" (.lit 0)) (.while (.lt (.var "row.v") (.var "graph.n")) countStep))

theorem count_command_spec {n : ℕ} (B : ℕ) (A J : Finset (Fin n)) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "row.mask"=mask A ∧ σ.vars "column.mask"=mask J)
      countCommand (fun _ τ => τ.vars "coefficient.positive"=matchCount A J n) (22*n+8) := by
  have hloop := Spec.forRangeZero "row.v" "graph.n" (CountInvariant A J) n 18 (by omega)
    (fun _ h => h.2.2.2.1) (fun _ h => h.1) (count_step_spec B A J hB hm)
  rintro σ ⟨hn,hA,hJ⟩
  let ν := σ.setVar "coefficient.positive" 0
  have r1 : Run B (.assign "coefficient.positive" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have r0 : Run B (.assign "row.v" (.lit 0)) ν (ν.setVar "row.v" 0) 2 := Run.assign (evalB_lit (by omega))
  have hi : CountInvariant A J (ν.setVar "row.v" 0) := by
    refine ⟨?_,?_,?_,by simp,?_⟩
    · exact ((r1.seq r0).frame_var "graph.n" (by decide)).trans hn
    · exact ((r1.seq r0).frame_var "row.mask" (by decide)).trans hA
    · exact ((r1.seq r0).frame_var "column.mask" (by decide)).trans hJ
    · change 0=matchCount A J 0
      exact (matches_zero A J).symm
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),by simpa only [p2.2] using p2.1.2.2.2.2⟩

def massCommand : Com := .seq countCommand (.seq (compare "coefficient.negative" "row.mask" "column.mask")
  (.assign "coefficient.negative" (.mul (.var "row.k") (.var "coefficient.negative"))))

theorem mass_spec {n : ℕ} (B : ℕ) (A J : Finset (Fin n)) (k : ℕ) (hB : n+2<B) (hk : k<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "row.mask"=mask A ∧ σ.vars "column.mask"=mask J ∧ σ.vars "row.k"=k)
      massCommand (fun _ τ => τ.vars "coefficient.positive"=matchCount A J n ∧ τ.vars "coefficient.negative"=k*same A J)
      (22*n+18) := by
  rintro σ ⟨hn,hA,hJ,hkσ⟩
  obtain ⟨ν,r1,p1⟩ := count_command_spec B A J hB hm σ ⟨hn,hA,hJ⟩
  obtain ⟨μ,r2,p2⟩ := compare_spec B (mask A) (mask J) "coefficient.negative" "row.mask" "column.mask"
    ((mask_bound _).trans hm) ((mask_bound _).trans hm) (by omega) ν
    ⟨(r1.frame_var "row.mask" (by decide)).trans hA,(r1.frame_var "column.mask" (by decide)).trans hJ⟩
  have hb : μ.vars "coefficient.negative"=same A J := by simpa only [same_masks] using p2
  have r12 := r1.seq r2
  have hkμ : μ.vars "row.k"=k := (r12.frame_var "row.k" (by decide)).trans hkσ
  have hprod : k*same A J<B := (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (same_le A J) : k*same A J≤k).trans_lt hk
  let τ := μ.setVar "coefficient.negative" (k*same A J)
  have r3 : Run B (.assign "coefficient.negative" (.mul (.var "row.k") (.var "coefficient.negative"))) μ τ 4 := Run.assign
    (evalB_bin (op := .mul)
      (by rw [evalB_var_iff]; exact ⟨hkμ.symm,hkμ ▸ hk⟩)
      (by rw [evalB_var_iff]; exact ⟨hb.symm,hb ▸ (same_le A J).trans_lt (by omega)⟩) hprod)
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),?_,by simp [τ]⟩
  exact ((r2.seq r3).frame_var "coefficient.positive" (by decide)).trans p1

end Lax263307Proofs.NativeMomentRows
