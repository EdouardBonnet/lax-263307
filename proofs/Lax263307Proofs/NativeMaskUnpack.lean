import Lax263307Proofs.NativeCatalog

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMaskUnpack

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open NativeMasks

theorem bit_value {n : ℕ} (I : Finset (Fin n)) (v : Fin n) :
    Nat.land (mask I / 2^v.val) 1=if v∈I then 1 else 0 := by
  rw [Nat.land_eq,Nat.and_one_is_mod]
  have h := mask_member I v
  rw [Nat.testBit_eq_decide_div_mod_eq] at h
  have hm := Nat.mod_lt (mask I / 2^v.val) (by omega : 0<2)
  by_cases hv : v∈I
  · simp only [hv,decide_true,decide_eq_true_eq,if_true] at h ⊢
    exact h
  · simp only [hv,decide_false,decide_eq_false_iff_not,if_false] at h ⊢
    omega

theorem prefix_card_step {n : ℕ} (I : Finset (Fin n)) (i : ℕ) (hi : i<n) :
    (initialSet I (i+1)).card=(initialSet I i).card+(if (⟨i,hi⟩ : Fin n)∈I then 1 else 0) := by
  rw [prefix_succ I i hi]
  have hm : (⟨i,hi⟩ : Fin n)∉initialSet I i := by simp [initialSet]
  by_cases h : (⟨i,hi⟩ : Fin n)∈I <;> simp [h,Finset.card_insert_of_notMem hm]

theorem card_bound {n : ℕ} (I : Finset (Fin n)) : I.card≤n := by
  simpa using Finset.card_le_univ I

def read : Com := .assign "unpack.bit" (.and (.shiftr (.var "unpack.mask") (.var "unpack.i")) (.lit 1))

def step : Com := .seq read (.seq (.assign "unpack.card" (.add (.var "unpack.card") (.var "unpack.bit")))
  (Lax455465Proofs.RamWordBuffer.append "subset.bits" "unpack.i" (.var "unpack.bit")))

def Invariant {n : ℕ} (I : Finset (Fin n)) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "unpack.mask"=mask I ∧ σ.vars "unpack.i"≤n ∧
  n≤(σ.arrs "subset.bits").length ∧
  Prefix ((encodeOutput I).take (σ.vars "unpack.i")) "subset.bits" σ ∧
  σ.vars "unpack.card"=(initialSet I (σ.vars "unpack.i")).card

theorem step_spec {n : ℕ} (B : ℕ) (I : Finset (Fin n)) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => Invariant I σ ∧ σ.vars "unpack.i"<n) step
      (fun σ τ => Invariant I τ ∧ τ.vars "unpack.i"=σ.vars "unpack.i"+1) 17 := by
  rintro σ ⟨⟨hn,hmask,hle,hroom,hprefix,hcard⟩,hlt⟩
  let i := σ.vars "unpack.i"
  let bit := if (⟨i,hlt⟩ : Fin n)∈I then 1 else 0
  have hbit : bit≤1 := by dsimp [bit]; split_ifs <;> omega
  have hbitB : bit<B := by omega
  have hiB : i<B := by omega
  have hmaskB : mask I<B := (mask_bound I).trans hm
  have hdiv : mask I/2^i<B := (Nat.div_le_self _ _).trans_lt hmaskB
  have hval : (Expr.and (.shiftr (.var "unpack.mask") (.var "unpack.i")) (.lit 1)).evalB B σ=some bit := by
    have hh := evalB_bin (op := .and)
      (evalB_bin (op := .shiftr)
        (by rw [evalB_var_iff]; exact ⟨hmask.symm,hmask ▸ hmaskB⟩) (evalB_var hiB) hdiv)
      (evalB_lit (show 1<B by omega)) (by change Nat.land (mask I/2^i) 1<B; rw [bit_value I ⟨i,hlt⟩]; exact hbitB)
    exact hh.trans (congrArg some (bit_value I ⟨i,hlt⟩))
  let ν := σ.setVar "unpack.bit" bit
  have r1 : Run B read σ ν 6 := Run.assign hval
  have hcardν : ν.vars "unpack.card"=(initialSet I i).card :=
    (r1.frame_var "unpack.card" (by decide)).trans hcard
  have hnextB : (initialSet I (i+1)).card<B := (card_bound _).trans_lt (by omega)
  have hsum : (initialSet I i).card+bit<B := by rw [←prefix_card_step I i hlt]; exact hnextB
  let μ := ν.setVar "unpack.card" ((initialSet I i).card+bit)
  have r2 : Run B (.assign "unpack.card" (.add (.var "unpack.card") (.var "unpack.bit"))) ν μ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hcardν.symm,hcardν ▸ (card_bound _).trans_lt (by omega)⟩)
      (by simpa [ν] using evalB_var (σ:=ν) (x:="unpack.bit") (show ν.vars "unpack.bit"<B by simp [ν]; exact hbitB)) hsum)
  have r12 := r1.seq r2
  have hiμ : μ.vars "unpack.i"=i := r12.frame_var "unpack.i" (by decide)
  have hbitμ : μ.vars "unpack.bit"=bit := by simp [μ,ν]
  have hlen : (encodeOutput I).length=n := List.length_ofFn
  have hilen : i<(encodeOutput I).length := by rwa [hlen]
  have htake : ((encodeOutput I).take i).length=i := by rw [List.length_take,hlen,Nat.min_eq_left hle]
  have hentry : (encodeOutput I)[i]=bit := by simp [encodeOutput,bit]
  obtain ⟨τ,r3,p3⟩ := Lax455465Proofs.RamWordBuffer.append_spec B "subset.bits" "unpack.i"
    ((encodeOutput I).take i) bit (.var "unpack.bit") (by omega) (by rw [htake]; omega) μ
    ⟨by simpa only [Prefix,r12.frame_arr "subset.bits" (by decide)] using hprefix,
      by rwa [htake],by rw [htake,Lax455465Proofs.RamFrames.run_array_length r12]; omega,
      by rw [evalB_var_iff]; exact ⟨hbitμ.symm,hbitμ ▸ hbitB⟩⟩
  have ht : τ.vars "unpack.i"=i+1 := by simpa only [htake] using p3.2
  have rr := r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "graph.n" (by decide)).trans hn,
    (rr.frame_var "unpack.mask" (by decide)).trans hmask,by rw [ht]; omega,?_,?_,?_⟩
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem hilen,hentry]
    exact p3.1
  · rw [ht,prefix_card_step I i hlt,r3.frame_var "unpack.card" (by decide)]
    simp [μ,bit]

def command : Com := .seq (.assign "unpack.card" (.lit 0))
  (.seq (.assign "unpack.i" (.lit 0)) (.while (.lt (.var "unpack.i") (.var "graph.n")) step))

theorem command_spec {n : ℕ} (B : ℕ) (I : Finset (Fin n)) (hB : n+2<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "unpack.mask"=mask I ∧ n≤(σ.arrs "subset.bits").length)
      command (fun _ τ => Prefix (encodeOutput I) "subset.bits" τ ∧ τ.vars "unpack.card"=I.card) (21*n+8) := by
  have hloop := Spec.forRangeZero "unpack.i" "graph.n" (Invariant I) n 17 (by omega)
    (fun _ h => h.2.2.1) (fun _ h => h.1) (step_spec B I hB hm)
  rintro σ ⟨hn,hmask,hroom⟩
  let ν := σ.setVar "unpack.card" 0
  have r1 : Run B (.assign "unpack.card" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hi : Invariant I (ν.setVar "unpack.i" 0) := by
    refine ⟨?_,?_,by simp,hroom,?_,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hmask
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
    · simp [ν,prefix_zero]
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by omega),?_,?_⟩
  · have htake : (encodeOutput I).take n=encodeOutput I := List.take_of_length_le (by simp [encodeOutput])
    simpa only [p2.2,htake] using p2.1.2.2.2.2.1
  · simpa only [p2.2,prefix_full] using p2.1.2.2.2.2.2

end Lax263307Proofs.NativeMaskUnpack
