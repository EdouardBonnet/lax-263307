import Lax263307.WeightedAlgorithm
import Lax808846.Ram
import Lax263307Proofs.NativeWeightReduction
import Mathlib.Data.Fin.Tuple.Take

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeBlowUp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307.WeightedAlgorithm

def blocks {n : ℕ} (copies : Fin n → ℕ) : List (List ℕ) :=
  List.ofFn fun v => List.replicate (copies v) v.val

def owners {n : ℕ} (copies : Fin n → ℕ) : List ℕ := (blocks copies).flatten

theorem blocks_length {n : ℕ} (copies : Fin n → ℕ) : (blocks copies).length=n := by
  simp [blocks]

theorem owners_length {n : ℕ} (copies : Fin n → ℕ) : (owners copies).length=∑ v,copies v := by
  simp [owners,blocks,List.length_flatten,List.map_ofFn,List.sum_ofFn]

theorem flattened_coordinate {α : Type*} (xs : List (List α)) (i : ℕ) (hi : i<xs.length)
    (j : ℕ) (hj : j<xs[i].length) :
    xs.flatten[((xs.take i).map List.length).sum+j]?=some xs[i][j] := by
  have he : xs=xs.take i++xs[i]::xs.drop (i+1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hf : xs.flatten=(xs.take i).flatten++xs[i]++(xs.drop (i+1)).flatten := by
    conv_lhs => rw [he]
    simp only [List.flatten_append,List.flatten_cons,List.append_assoc]
  rw [hf,List.append_assoc]
  rw [List.getElem?_append_right (by rw [List.length_flatten]; omega)]
  rw [List.length_flatten]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left hj,List.getElem?_eq_getElem hj]

theorem owners_coordinate {n : ℕ} (copies : Fin n → ℕ)
    (v : Fin n) (j : Fin (copies v)) :
    (owners copies)[(finSigmaFinEquiv ⟨v,j⟩).val]?=some v.val := by
  have hi : v.val<(blocks copies).length := by rw [blocks_length]; exact v.isLt
  have hb : (blocks copies)[v.val]=List.replicate (copies v) v.val := by
    simp [blocks]
  have hp : ((blocks copies).take v.val).map List.length =
      List.ofFn (fun i : Fin v.val => copies (Fin.castLE v.isLt.le i)) := by
    rw [List.map_take]
    have hm : (blocks copies).map List.length=List.ofFn copies := by
      rw [blocks,List.map_ofFn]
      congr 1
      funext v
      exact List.length_replicate
    rw [hm]
    exact (Fin.ofFn_take_eq_take_ofFn v.isLt.le copies).symm
  have hx := flattened_coordinate (blocks copies) v.val hi j.val (by simpa only [hb,List.length_replicate] using j.isLt)
  simpa only [owners,finSigmaFinEquiv_apply,hp,List.sum_ofFn,hb,List.getElem_replicate] using hx

theorem owners_labeling {n : ℕ} (copies : Fin n → ℕ) (i : Fin (∑ v,copies v)) :
    (owners copies)[i.val]?=some (labeling copies i).1.val := by
  have hx := owners_coordinate copies (labeling copies i).1 (labeling copies i).2
  simpa only [labeling,Sigma.eta,Equiv.apply_symm_apply] using hx

def repeatStep : Com := .seq
  (Lax455465Proofs.RamWordBuffer.append "blowup.owner" "blowup.length" (.var "owner.value"))
  (.assign "owner.j" (.add (.var "owner.j") (.lit 1)))

def repeatCommand : Com := .seq (.assign "owner.j" (.lit 0))
  (.while (.lt (.var "owner.j") (.var "owner.count")) repeatStep)

def RepeatInvariant (xs : List ℕ) (v count : ℕ) (σ : Env) : Prop :=
  σ.vars "owner.j"≤count ∧ σ.vars "owner.count"=count ∧ σ.vars "owner.value"=v ∧
  σ.vars "blowup.length"=xs.length+σ.vars "owner.j" ∧
  xs.length+count≤(σ.arrs "blowup.owner").length ∧
  Prefix (xs++List.replicate (σ.vars "owner.j") v) "blowup.owner" σ

theorem repeat_step_spec (B : ℕ) (xs : List ℕ) (v count : ℕ)
    (hB : xs.length+count+2<B) (hv : v<B) :
    Spec B (fun σ => RepeatInvariant xs v count σ ∧ σ.vars "owner.j"<count)
      repeatStep (fun σ τ => RepeatInvariant xs v count τ ∧ τ.vars "owner.j"=σ.vars "owner.j"+1) 11 := by
  rintro σ ⟨⟨hj,hcount,hvσ,hlen,hroom,hprefix⟩,hlt⟩
  let j := σ.vars "owner.j"
  have hl : (xs++List.replicate j v).length=xs.length+j := by simp
  obtain ⟨ν,r1,p1⟩ := Lax455465Proofs.RamWordBuffer.append_spec B "blowup.owner" "blowup.length"
    (xs++List.replicate j v) v (.var "owner.value") (by omega) (by rw [hl]; omega) σ
    ⟨hprefix,by rwa [hl],by rw [hl]; omega,by rw [evalB_var_iff]; exact ⟨hvσ.symm,hvσ ▸ hv⟩⟩
  have hjν : ν.vars "owner.j"=j := r1.frame_var "owner.j" (by decide)
  have he : (Expr.add (.var "owner.j") (.lit 1)).evalB B ν=some (j+1) :=
    evalB_bin (op := .add) (by rw [evalB_var_iff]; exact ⟨hjν.symm,hjν ▸ (by omega)⟩)
      (evalB_lit (by omega)) (by change j+1<B; dsimp [j]; omega)
  let τ := ν.setVar "owner.j" (j+1)
  have r2 : Run B (.assign "owner.j" (.add (.var "owner.j") (.lit 1))) ν τ 4 := Run.assign he
  have rr := r1.seq r2
  have ht : τ.vars "owner.j"=j+1 := by simp [τ]
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨by rw [ht]; omega,(rr.frame_var "owner.count" (by decide)).trans hcount,
    (rr.frame_var "owner.value" (by decide)).trans hvσ,?_,?_,?_⟩
  · rw [r2.frame_var "blowup.length" (by decide),p1.2,hl,ht]
    omega
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht]
    have hx : xs++List.replicate j v++[v]=xs++List.replicate (j+1) v := by
      rw [List.replicate_add]
      simp only [List.replicate_one,List.append_assoc]
    simpa only [Prefix,τ,arrs_setVar,hx] using p1.1

theorem repeat_spec (B : ℕ) (xs : List ℕ) (v count : ℕ)
    (hB : xs.length+count+2<B) (hv : v<B) :
    Spec B (fun σ => σ.vars "owner.count"=count ∧ σ.vars "owner.value"=v ∧
      σ.vars "blowup.length"=xs.length ∧ xs.length+count≤(σ.arrs "blowup.owner").length ∧
      Prefix xs "blowup.owner" σ) repeatCommand
      (fun _ τ => Prefix (xs++List.replicate count v) "blowup.owner" τ ∧
        τ.vars "blowup.length"=xs.length+count) (15*count+6) := by
  have hloop := Spec.forRangeZero "owner.j" "owner.count" (RepeatInvariant xs v count)
    count 11 (by omega) (fun _ h => h.1) (fun _ h => h.2.1) (repeat_step_spec B xs v count hB hv)
  rintro σ ⟨hc,hvσ,hlen,hroom,hprefix⟩
  have hi : RepeatInvariant xs v count (σ.setVar "owner.j" 0) := by
    refine ⟨by simp,?_,?_,?_,hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hc
    · simpa only [vars_setVar,String.reduceEq,if_false] using hvσ
    · simpa only [vars_setVar,String.reduceEq,if_true,if_false,Nat.add_zero] using hlen
    · simpa only [vars_setVar,if_true,List.replicate_zero,List.append_nil,Prefix,arrs_setVar] using hprefix
  obtain ⟨τ,rr,hpost⟩ := hloop σ hi
  refine ⟨τ,rr,?_,?_⟩
  · simpa only [hpost.2] using hpost.1.2.2.2.2.2
  · simpa only [hpost.2] using hpost.1.2.2.2.1

def ownerPrefix {n : ℕ} (copies : Fin n → ℕ) (i : ℕ) : List ℕ :=
  ((blocks copies).take i).flatten

theorem partial_length_le {n : ℕ} (copies : Fin n → ℕ) (i : ℕ) :
    (ownerPrefix copies i).length≤∑ v,copies v := by
  have he : owners copies=ownerPrefix copies i++((blocks copies).drop i).flatten := by
    rw [owners,ownerPrefix,←List.flatten_append,List.take_append_drop]
  have hh := congrArg List.length he
  rw [owners_length,List.length_append] at hh
  omega

theorem partial_succ {n : ℕ} (copies : Fin n → ℕ) (i : ℕ) (hi : i<n) :
    ownerPrefix copies (i+1)=ownerPrefix copies i++List.replicate (copies ⟨i,hi⟩) i := by
  unfold ownerPrefix
  rw [List.take_succ_eq_append_getElem (by rwa [blocks_length]),List.flatten_append]
  simp [blocks]

def ownerPrepare : Com := .seq (.assign "owner.value" (.var "owner.i"))
  (.assign "owner.count" (.get "copy.counts" (.var "owner.i")))

def ownerStep : Com := .seq ownerPrepare (.seq repeatCommand
  (.assign "owner.i" (.add (.var "owner.i") (.lit 1))))

def OwnerInvariant {n : ℕ} (copies : Fin n → ℕ) (σ : Env) : Prop :=
  σ.vars "owner.i"≤n ∧ σ.vars "input.n"=n ∧
  Prefix (List.ofFn copies) "copy.counts" σ ∧
  (∑ v,copies v)≤(σ.arrs "blowup.owner").length ∧
  σ.vars "blowup.length"=(ownerPrefix copies (σ.vars "owner.i")).length ∧
  Prefix (ownerPrefix copies (σ.vars "owner.i")) "blowup.owner" σ

theorem owner_step_spec {n : ℕ} (B : ℕ) (copies : Fin n → ℕ)
    (hB : n+(∑ v,copies v)+3<B) :
    Spec B (fun σ => OwnerInvariant copies σ ∧ σ.vars "owner.i"<n) ownerStep
      (fun σ τ => OwnerInvariant copies τ ∧ τ.vars "owner.i"=σ.vars "owner.i"+1)
      (15*(∑ v,copies v)+15) := by
  rintro σ ⟨⟨hle,hn,hcounts,hroom,hlen,hprefix⟩,hlt⟩
  let i := σ.vars "owner.i"
  let v : Fin n := ⟨i,hlt⟩
  let xs := ownerPrefix copies i
  have hs := partial_length_le copies (i+1)
  rw [partial_succ copies i hlt,List.length_append,List.length_replicate] at hs
  have hcB : copies v<B := by dsimp [v] at *; omega
  have hiB : i<B := by omega
  have hd : (σ.arrs "copy.counts")[i]?=some (copies v) := by
    have hh := hcounts i (by simpa using hlt)
    rw [List.getElem_ofFn] at hh
    exact hh
  have prep : Spec B (fun σ => σ.vars "owner.i"=i ∧ (σ.arrs "copy.counts")[i]?=some (copies v))
      ownerPrepare (fun _ τ => τ.vars "owner.value"=i ∧ τ.vars "owner.count"=copies v) 5 := by
    rintro σ ⟨hsi,hsval⟩
    have hroom : i<(σ.arrs "copy.counts").length := by
      by_contra hh
      rw [List.getElem?_eq_none (by omega)] at hsval
      contradiction
    run_vcg
    all_goals simp_all [Env.setVar]
  obtain ⟨ν,r1,p1⟩ := prep σ ⟨rfl,hd⟩
  obtain ⟨μ,r2,p2⟩ := repeat_spec B xs i (copies v) (by dsimp [xs,v]; omega) hiB ν
    ⟨p1.2,p1.1,(r1.frame_var "blowup.length" (by decide)).trans hlen,
      by rw [Lax455465Proofs.RamFrames.run_array_length r1]; exact hs.trans hroom,
      by simpa only [Prefix,r1.frame_arr "blowup.owner" (by decide)] using hprefix⟩
  have r12 := r1.seq r2
  have hiμ : μ.vars "owner.i"=i := r12.frame_var "owner.i" (by decide)
  let τ := μ.setVar "owner.i" (i+1)
  have r3 : Run B (.assign "owner.i" (.add (.var "owner.i") (.lit 1))) μ τ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩)
      (evalB_lit (by omega)) (by change i+1<B; dsimp [i]; omega))
  have rr := r1.seq (r2.seq r3)
  have ht : τ.vars "owner.i"=i+1 := by simp [τ]
  refine ⟨τ,rr.mono (by dsimp [v] at *; omega),?_,ht⟩
  refine ⟨by rw [ht]; omega,(rr.frame_var "input.n" (by decide)).trans hn,?_,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "copy.counts" (by decide)] using hcounts
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,partial_succ copies i hlt,List.length_append,List.length_replicate]
    exact (r3.frame_var "blowup.length" (by decide)).trans p2.2
  · rw [ht,partial_succ copies i hlt]
    simpa only [Prefix,r3.frame_arr "blowup.owner" (by decide)] using p2.1

def ownerCommand : Com := .seq (.assign "blowup.length" (.lit 0))
  (.seq (.assign "owner.i" (.lit 0)) (.while (.lt (.var "owner.i") (.var "input.n")) ownerStep))

theorem owner_command_spec {n : ℕ} (B : ℕ) (copies : Fin n → ℕ)
    (hB : n+(∑ v,copies v)+3<B) :
    Spec B (fun σ => σ.vars "input.n"=n ∧ Prefix (List.ofFn copies) "copy.counts" σ ∧
      (∑ v,copies v)≤(σ.arrs "blowup.owner").length) ownerCommand
      (fun _ τ => Prefix (owners copies) "blowup.owner" τ ∧ τ.vars "blowup.length"=∑ v,copies v)
      ((15*(∑ v,copies v)+19)*n+8) := by
  have hloop := Spec.forRangeZero "owner.i" "input.n" (OwnerInvariant copies) n
    (15*(∑ v,copies v)+15) (by omega) (fun _ h => h.1) (fun _ h => h.2.1)
    (owner_step_spec B copies hB)
  rintro σ ⟨hn,hcounts,hroom⟩
  let ν := σ.setVar "blowup.length" 0
  have r1 : Run B (.assign "blowup.length" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hi : OwnerInvariant copies (ν.setVar "owner.i" 0) := by
    refine ⟨by simp,?_,hcounts,hroom,?_,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simp [ν,ownerPrefix]
    · simp only [vars_setVar,if_true,ownerPrefix,List.take_zero,List.flatten_nil,Prefix,List.length_nil]
      intro j hj
      omega
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  have he : ownerPrefix copies n=owners copies := by
    unfold ownerPrefix owners
    rw [List.take_of_length_le (by rw [blocks_length])]
  refine ⟨τ,(r1.seq r2).mono (by nlinarith),?_,?_⟩
  · simpa only [p2.2,he] using p2.1.2.2.2.2.2
  · simpa only [p2.2,he,owners_length] using p2.1.2.2.2.2.1

def matrix {n : ℕ} (f : Fin n → Fin n → ℕ) : List ℕ :=
  (List.ofFn fun i => List.ofFn (f i)).flatten

theorem matrix_length {n : ℕ} (f : Fin n → Fin n → ℕ) : (matrix f).length=n*n := by
  simp [matrix,List.length_flatten,List.map_ofFn,List.sum_ofFn,Finset.sum_const]

theorem matrix_coordinate {n : ℕ} (f : Fin n → Fin n → ℕ) (i j : Fin n) :
    (matrix f)[i.val*n+j.val]?=some (f i j) := by
  let xs := List.ofFn fun i => List.ofFn (f i)
  have hi : i.val<xs.length := by simpa only [xs,List.length_ofFn] using i.isLt
  have hj : j.val<xs[i.val].length := by simpa only [xs,List.getElem_ofFn,List.length_ofFn] using j.isLt
  have hx := flattened_coordinate xs i.val hi j.val hj
  have hp : ((xs.take i.val).map List.length).sum=i.val*n := by
    rw [List.map_take]
    have hm : xs.map List.length=List.replicate n n := by
      dsimp only [xs]
      rw [List.map_ofFn,←List.ofFn_const]
      congr 1
      funext v
      exact List.length_ofFn
    rw [hm]
    simp [List.take_replicate,List.sum_replicate]
  simpa only [hp,matrix,xs,List.getElem_ofFn] using hx

def row {n : ℕ} (q : Fin (n*n)) : Fin n := ⟨q.val/n, by
  have hn : 0<n := by nlinarith only [q.isLt]
  exact (Nat.div_lt_iff_lt_mul hn).mpr q.isLt⟩

def col {n : ℕ} (q : Fin (n*n)) : Fin n := ⟨q.val%n, by
  have hn : 0<n := by nlinarith only [q.isLt]
  exact Nat.mod_lt _ hn⟩

theorem matrix_flat_coordinate {n : ℕ} (f : Fin n → Fin n → ℕ) (q : Fin (n*n)) :
    (matrix f)[q.val]?=some (f (row q) (col q)) := by
  have hx := matrix_coordinate f (row q) (col q)
  have he : (row q).val*n+(col q).val=q.val := by
    simpa only [row,col,Nat.mul_comm] using Nat.div_add_mod q.val n
  rwa [he] at hx

def matrixEntry : Com :=
  .seq (.assign "matrix.u" (.get "blowup.owner" (.div (.var "matrix.i") (.var "blowup.length"))))
  (.seq (.assign "matrix.v" (.get "blowup.owner" (.sub (.var "matrix.i") (.mul (.div (.var "matrix.i") (.var "blowup.length")) (.var "blowup.length")))))
    (.assign "matrix.entry" (.get "input.data"
      (.add (.mul (.var "matrix.u") (.var "input.n")) (.var "matrix.v")))))

theorem matrix_entry_spec (B n N q u v entry : ℕ) (hB : n*n+N*N+n+N+3<B)
    (hq : q<N*N) (hu : u<n) (hv : v<n) (he : entry<B) :
    Spec B (fun σ => σ.vars "input.n"=n ∧ σ.vars "blowup.length"=N ∧ σ.vars "matrix.i"=q ∧
      (σ.arrs "blowup.owner")[q/N]?=some u ∧ (σ.arrs "blowup.owner")[q%N]?=some v ∧
      (σ.arrs "input.data")[u*n+v]?=some entry) matrixEntry
      (fun _ τ => τ.vars "matrix.entry"=entry) 21 := by
  have hN : 0<N := by nlinarith only [hq]
  have hqN : q/N<N := (Nat.div_lt_iff_lt_mul hN).mpr hq
  have hrN : q%N<N := Nat.mod_lt _ hN
  have hidx : u*n+v<n*n := by nlinarith only [hu,hv]
  have hmul : u*n<B := by omega
  have hdivmul : q/N*N≤q := Nat.div_mul_le_self q N
  have hmod : q-q/N*N=q%N := (Nat.mod_eq_sub_div_mul).symm
  rintro σ ⟨hn,hNσ,hqσ,huσ,hvσ,heσ⟩
  have hroomu : q/N<(σ.arrs "blowup.owner").length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at huσ
    contradiction
  have hroomv : q%N<(σ.arrs "blowup.owner").length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hvσ
    contradiction
  have hroome : u*n+v<(σ.arrs "input.data").length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at heσ
    contradiction
  run_vcg
  all_goals simp_all [Env.setVar,←Nat.mod_eq_sub_div_mul]
  all_goals omega

def matrixStep : Com := .seq matrixEntry
  (Lax455465Proofs.RamWordBuffer.append "blowup.matrix" "matrix.i" (.var "matrix.entry"))

def numberedMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies : Fin n → ℕ) : List ℕ := matrix (fun i j => if (numbered G copies).Adj i j then 1 else 0)

def MatrixInvariant {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies : Fin n → ℕ) (σ : Env) : Prop :=
  σ.vars "input.n"=n ∧ σ.vars "blowup.length"=∑ v,copies v ∧
  σ.vars "matrix.length"=(∑ v,copies v)*(∑ v,copies v) ∧
  σ.vars "matrix.i"≤(numberedMatrix G copies).length ∧
  Prefix (NativeWeightReduction.adjacency G) "input.data" σ ∧
  Prefix (owners copies) "blowup.owner" σ ∧
  (numberedMatrix G copies).length≤(σ.arrs "blowup.matrix").length ∧
  Prefix ((numberedMatrix G copies).take (σ.vars "matrix.i")) "blowup.matrix" σ

theorem matrix_step_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies : Fin n → ℕ) (hB : n*n+(∑ v,copies v)*(∑ v,copies v)+n+(∑ v,copies v)+3<B) :
    Spec B (fun σ => MatrixInvariant G copies σ ∧ σ.vars "matrix.i"<(numberedMatrix G copies).length)
      matrixStep (fun σ τ => MatrixInvariant G copies τ ∧ τ.vars "matrix.i"=σ.vars "matrix.i"+1) 28 := by
  rintro σ ⟨⟨hn,hN,hlen,hle,hgraph,howners,hroom,hprefix⟩,hlt⟩
  let N := ∑ v,copies v
  let xs := numberedMatrix G copies
  let q := σ.vars "matrix.i"
  have hxs : xs.length=N*N := matrix_length _
  have hq : q<N*N := by simpa only [←hxs] using hlt
  let i := row (⟨q,hq⟩ : Fin (N*N))
  let j := col (⟨q,hq⟩ : Fin (N*N))
  let u := (labeling copies i).1
  let v := (labeling copies j).1
  let entry := if G.Adj u v then 1 else 0
  have hentry : entry<B := by dsimp [entry]; split_ifs <;> omega
  have hou : (σ.arrs "blowup.owner")[q/N]?=some u.val := by
    have hh := howners i.val (by rw [owners_length]; exact i.isLt)
    have ho := owners_labeling copies i
    have ht := List.getElem?_eq_getElem (by rw [owners_length]; exact i.isLt : i.val<(owners copies).length)
    rw [ht] at ho
    exact hh.trans ho
  have hov : (σ.arrs "blowup.owner")[q%N]?=some v.val := by
    have hh := howners j.val (by rw [owners_length]; exact j.isLt)
    have ho := owners_labeling copies j
    have ht := List.getElem?_eq_getElem (by rw [owners_length]; exact j.isLt : j.val<(owners copies).length)
    rw [ht] at ho
    exact hh.trans ho
  have hidx : u.val*n+v.val<n*n := by nlinarith only [u.isLt,v.isLt]
  have hedge : (σ.arrs "input.data")[u.val*n+v.val]?=some entry := by
    have hh := hgraph (u.val*n+v.val) (by rwa [NativeWeightReduction.adjacency_length])
    have hc := matrix_coordinate (fun u v => if G.Adj u v then 1 else 0) u v
    rw [List.getElem?_eq_getElem (by rwa [matrix_length])] at hc
    exact hh.trans hc
  obtain ⟨ν,r1,p1⟩ := matrix_entry_spec B n N q u.val v.val entry hB hq u.isLt v.isLt hentry σ
    ⟨hn,hN,rfl,hou,hov,hedge⟩
  have hqν : ν.vars "matrix.i"=q := r1.frame_var "matrix.i" (by decide)
  have htake : (xs.take q).length=q := by rw [List.length_take]; omega
  have hval : xs[q]=entry := by
    have hc := matrix_flat_coordinate (fun i j => if (numbered G copies).Adj i j then 1 else 0)
      (⟨q,hq⟩ : Fin (N*N))
    change xs[q]?=some entry at hc
    rw [List.getElem?_eq_getElem hlt] at hc
    exact Option.some.inj hc
  obtain ⟨τ,r2,p2⟩ := Lax455465Proofs.RamWordBuffer.append_spec B "blowup.matrix" "matrix.i"
    (xs.take q) entry (.var "matrix.entry") (by omega) (by rw [htake]; dsimp [N] at hq; omega) ν
    ⟨by simpa only [Prefix,r1.frame_arr "blowup.matrix" (by decide)] using hprefix,
      by rwa [htake],by rw [htake,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ hentry⟩⟩
  have ht : τ.vars "matrix.i"=q+1 := by simpa only [htake] using p2.2
  have rr := r1.seq r2
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "input.n" (by decide)).trans hn,
    (rr.frame_var "blowup.length" (by decide)).trans hN,
    (rr.frame_var "matrix.length" (by decide)).trans hlen,by rw [ht]; omega,?_,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "input.data" (by decide)] using hgraph
  · simpa only [Prefix,rr.frame_arr "blowup.owner" (by decide)] using howners
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem hlt,hval]
    exact p2.1

def matrixCommand : Com := .seq
  (.assign "matrix.length" (.mul (.var "blowup.length") (.var "blowup.length")))
  (.seq (.assign "matrix.i" (.lit 0))
    (.while (.lt (.var "matrix.i") (.var "matrix.length")) matrixStep))

theorem matrix_command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies : Fin n → ℕ) (hB : n*n+(∑ v,copies v)*(∑ v,copies v)+n+(∑ v,copies v)+3<B) :
    Spec B (fun σ => σ.vars "input.n"=n ∧ σ.vars "blowup.length"=∑ v,copies v ∧
      Prefix (NativeWeightReduction.adjacency G) "input.data" σ ∧
      Prefix (owners copies) "blowup.owner" σ ∧
      (∑ v,copies v)*(∑ v,copies v)≤(σ.arrs "blowup.matrix").length) matrixCommand
      (fun _ τ => Prefix (numberedMatrix G copies) "blowup.matrix" τ)
      (32*(∑ v,copies v)*(∑ v,copies v)+10) := by
  let N := ∑ v,copies v
  have hlen : (numberedMatrix G copies).length=N*N := matrix_length _
  have hNB : N<B := by dsimp [N]; omega
  have hNNB : N*N<B := by dsimp [N]; omega
  have hloop := Spec.forRangeZero "matrix.i" "matrix.length" (MatrixInvariant G copies)
    (N*N) 28 hNNB (fun _ h => hlen ▸ h.2.2.2.1) (fun _ h => h.2.2.1)
    (by simpa only [hlen] using matrix_step_spec B G copies hB)
  rintro σ ⟨hn,hN,hgraph,howners,hroom⟩
  let ν := σ.setVar "matrix.length" (N*N)
  have r1 : Run B (.assign "matrix.length" (.mul (.var "blowup.length") (.var "blowup.length")))
      σ ν 4 := Run.assign (evalB_bin (op := .mul)
        (by rw [evalB_var_iff]; exact ⟨hN.symm,hN ▸ hNB⟩)
        (by rw [evalB_var_iff]; exact ⟨hN.symm,hN ▸ hNB⟩) hNNB)
  have hi : MatrixInvariant G copies (ν.setVar "matrix.i" 0) := by
    refine ⟨?_,?_,by simp [ν,N],by simp, hgraph,howners,?_,?_⟩
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hN
    · simpa only [arrs_setVar,ν,hlen] using hroom
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by dsimp [N]; nlinarith),?_⟩
  simpa only [p2.2,←hlen,List.take_length] using p2.1.2.2.2.2.2.2.2

def construct : Com := .seq ownerCommand matrixCommand

theorem construct_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies : Fin n → ℕ) (hB : n*n+(∑ v,copies v)*(∑ v,copies v)+n+(∑ v,copies v)+3<B) :
    Spec B (fun σ => σ.vars "input.n"=n ∧ Prefix (List.ofFn copies) "copy.counts" σ ∧
      Prefix (NativeWeightReduction.adjacency G) "input.data" σ ∧
      (∑ v,copies v)≤(σ.arrs "blowup.owner").length ∧
      (∑ v,copies v)*(∑ v,copies v)≤(σ.arrs "blowup.matrix").length) construct
      (fun _ τ => Prefix (numberedMatrix G copies) "blowup.matrix" τ ∧
        Prefix (owners copies) "blowup.owner" τ ∧ τ.vars "blowup.length"=∑ v,copies v)
      ((15*(∑ v,copies v)+19)*n+32*(∑ v,copies v)*(∑ v,copies v)+18) := by
  rintro σ ⟨hn,hcounts,hgraph,hownersroom,hmatrixroom⟩
  obtain ⟨ν,r1,p1⟩ := owner_command_spec B copies (by omega) σ ⟨hn,hcounts,hownersroom⟩
  obtain ⟨τ,r2,p2⟩ := matrix_command_spec B G copies hB ν
    ⟨(r1.frame_var "input.n" (by decide)).trans hn,p1.2,
      by simpa only [Prefix,r1.frame_arr "input.data" (by decide)] using hgraph,p1.1,
      by rwa [Lax455465Proofs.RamFrames.run_array_length r1]⟩
  refine ⟨τ,(r1.seq r2).mono (by omega),p2,?_,?_⟩
  · simpa only [Prefix,r2.frame_arr "blowup.owner" (by decide)] using p1.1
  · exact (r2.frame_var "blowup.length" (by decide)).trans p1.2

def prepare : Com := .seq NativeWeightReduction.prepare construct

open Lax263307.WeightRounding Lax263307.WeightedIndependentSet NativeFrontend

def cost (n N : ℕ) : ℕ := 12*(n*n+3*n+3)+110*n+78+(15*N+19)*n+32*N*N+18

theorem prepare_spec {n : ℕ} (B M : ℕ) (hM : 1≤M) (hn : n≤M)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → ℚ) (ε : ℚ) (hεpos : 0<ε)
    (hw : ∀ v,(w v).num.natAbs≤M ∧ (w v).den≤M) (hε : ε.num.natAbs≤M ∧ ε.den≤M)
    (hB : 2*M^4+3<B) (hsize : n*n+3*n+3<B)
    (hgraph : n*n+(∑ v,copies (fun v => max (w v) 0) ε v)^2+n+
      (∑ v,copies (fun v => max (w v) 0) ε v)+3<B) :
    let cs := copies (fun v => max (w v) 0) ε
    let N := ∑ v,cs v
    Spec B (fun σ => σ.inp=encodeInput G w ε ∧ n*n+3*n+3≤(σ.arrs "input.data").length ∧
      n≤(σ.arrs "copy.counts").length ∧ N≤(σ.arrs "blowup.owner").length ∧
      N*N≤(σ.arrs "blowup.matrix").length) prepare
      (fun σ τ => Prefix (numberedMatrix G cs) "blowup.matrix" τ ∧
        Prefix (owners cs) "blowup.owner" τ ∧ τ.vars "blowup.length"=N ∧
        Prefix (tailInput G w ε) "input.data" τ ∧ τ.out=σ.out ∧ τ.vars "input.n"=n) (cost n N) := by
  dsimp only
  let cs := copies (fun v => max (w v) 0) ε
  let N := ∑ v,cs v
  rintro σ ⟨hinp,hinputroom,hcountsroom,hownersroom,hmatrixroom⟩
  obtain ⟨ν,r1,hcounts,hnν,hout,hinput⟩ := NativeWeightReduction.prepare_spec B M hM hn
    G w ε hεpos hw hε hB hsize σ ⟨hinp,hinputroom,hcountsroom⟩
  have hfront : Prefix (NativeWeightReduction.adjacency G) "input.data" ν := by
    intro i hi
    have hfull : i<(tailInput G w ε).length := by
      rw [tail_length]
      rw [NativeWeightReduction.adjacency_length] at hi
      omega
    have hh := hinput i hfull
    have he : tailInput G w ε=NativeWeightReduction.adjacency G++encodeParameters w ε := rfl
    simpa only [he,List.getElem_append_left hi] using hh
  obtain ⟨τ,r2,p2⟩ := construct_spec B G cs (by simpa only [cs,pow_two] using hgraph) ν
    ⟨hnν,hcounts,hfront,by rwa [Lax455465Proofs.RamFrames.run_array_length r1],
      by rwa [Lax455465Proofs.RamFrames.run_array_length r1]⟩
  refine ⟨τ,(r1.seq r2).mono (by dsimp [cost,N,cs]; omega),p2.1,p2.2.1,p2.2.2,?_,?_,?_⟩
  · simpa only [Prefix,r2.frame_arr "input.data" (by decide)] using hinput
  · exact (r1.seq r2).out_eq (by decide)
  · exact (r2.frame_var _ (by decide)).trans hnν

def emit : Com := .seq (.write (.var "blowup.length"))
  (.seq (.assign "emit.count" (.mul (.var "blowup.length") (.var "blowup.length")))
    (Lax455465Proofs.RamEmitWords.command "blowup.matrix" 1))


def command : Com := .seq prepare emit

def totalCost (n N : ℕ) : ℕ := cost n N+13*N*N+12


open Lax109476Proofs

def layout := RamAutomaticLayout.layout command
def program : Lax808846.Ram.Program := Lax808846Proofs.Compile.compileProgram layout command


end Lax263307Proofs.NativeBlowUp
