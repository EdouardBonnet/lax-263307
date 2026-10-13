import Lax263307Proofs.NativeBlowUp
import Lax263307.ExhaustiveTargets

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeCombinations

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState

/-- Direct indexing in the exact order of `List.sublistsLen`; no powerset is built. -/
def select {α : Type*} : ℕ → List α → ℕ → List α
  | 0, _, _ => []
  | _+1, [], _ => []
  | k+1, a::xs, q =>
      if q<xs.length.choose (k+1) then select (k+1) xs q
      else a::select k xs (q-xs.length.choose (k+1))

theorem select_correct {α : Type*} (xs : List α) (k q : ℕ)
    (hq : q<xs.length.choose k) : (xs.sublistsLen k)[q]?=some (select k xs q) := by
  induction xs generalizing k q with
  | nil =>
    cases k with
    | zero =>
      have : q=0 := by simpa using hq
      subst q
      simp [select]
    | succ k => simp at hq
  | cons a xs ih =>
    cases k with
    | zero =>
      have : q=0 := by simpa using hq
      subst q
      simp [select]
    | succ k =>
      rw [List.sublistsLen_succ_cons]
      by_cases hh : q<xs.length.choose (k+1)
      · rw [List.getElem?_append_left (by rwa [List.length_sublistsLen])]
        simpa only [select,if_pos hh] using ih (k+1) q hh
      · rw [List.getElem?_append_right (by rw [List.length_sublistsLen]; omega)]
        rw [List.length_sublistsLen,List.getElem?_map]
        have hrem : q-xs.length.choose (k+1)<xs.length.choose k := by
          simp only [List.length_cons,Nat.choose_succ_succ,Nat.succ_eq_add_one] at hq
          omega
        rw [ih k _ hrem]
        simp only [Option.map_some,select,if_neg hh]

def table (n k : ℕ) : List ℕ :=
  (List.ofFn fun i : Fin (n+1) => List.ofFn fun j : Fin (k+1) => i.val.choose j.val).flatten

theorem table_length (n k : ℕ) : (table n k).length=(n+1)*(k+1) := by
  simp [table,List.length_flatten,List.map_ofFn,List.sum_ofFn,Finset.sum_const]
  ring

theorem table_coordinate (n k i j : ℕ) (hi : i≤n) (hj : j≤k) :
    (table n k)[i*(k+1)+j]?=some (i.choose j) := by
  let xs := List.ofFn fun i : Fin (n+1) => List.ofFn fun j : Fin (k+1) => i.val.choose j.val
  have hi' : i<xs.length := by simp only [xs,List.length_ofFn]; omega
  have hj' : j<xs[i].length := by simp only [xs,List.getElem_ofFn,List.length_ofFn]; omega
  have hh := NativeBlowUp.flattened_coordinate xs i hi' j hj'
  have hm : xs.map List.length=List.replicate (n+1) (k+1) := by
    dsimp only [xs]
    rw [List.map_ofFn,←List.ofFn_const]
    congr 1
    funext i
    exact List.length_ofFn
  have hp : ((xs.take i).map List.length).sum=i*(k+1) := by
    rw [List.map_take,hm]
    simp [List.take_replicate,List.sum_replicate,Nat.min_eq_left (by omega : i≤n+1)]
  simpa only [table,xs,hp,List.getElem_ofFn] using hh

def coordinates : Com :=
  .seq (.assign "choose.row" (.div (.var "choose.i") (.var "choose.cols")))
    (.assign "choose.col" (.sub (.var "choose.i")
      (.mul (.var "choose.row") (.var "choose.cols"))))

def entry : Com := .ite (.eq (.var "choose.col") (.lit 0))
  (.assign "choose.value" (.lit 1))
  (.ite (.eq (.var "choose.row") (.lit 0)) (.assign "choose.value" (.lit 0))
    (.seq (.assign "choose.prev" (.mul (.sub (.var "choose.row") (.lit 1)) (.var "choose.cols")))
      (.assign "choose.value" (.add
        (.get "choose.table" (.add (.var "choose.prev") (.sub (.var "choose.col") (.lit 1))))
        (.get "choose.table" (.add (.var "choose.prev") (.var "choose.col")))))))

def step : Com := .seq coordinates (.seq entry
  (Lax455465Proofs.RamWordBuffer.append "choose.table" "choose.i" (.var "choose.value")))

theorem coordinates_spec (B q d : ℕ) (_hd : 0<d) (hq : q<B) (hdB : d<B) :
    Spec B (fun σ => σ.vars "choose.i"=q ∧ σ.vars "choose.cols"=d) coordinates
      (fun _ τ => τ.vars "choose.row"=q/d ∧ τ.vars "choose.col"=q%d) 10 := by
  have hquot : q/d<B := (Nat.div_le_self _ _).trans_lt hq
  have hmul : q/d*d<B := (Nat.div_mul_le_self _ _).trans_lt hq
  have hrem : q-q/d*d<B := (Nat.sub_le _ _).trans_lt hq
  rintro σ ⟨hσq,hσd⟩
  run_vcg
  all_goals simp_all [Env.setVar,←Nat.mod_eq_sub_div_mul]

theorem entry_spec (B n k i j : ℕ) (hi : i≤n) (hj : j≤k)
    (hB : (n+1)*(k+1)+n+k+3<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (fun σ => σ.vars "choose.row"=i ∧ σ.vars "choose.col"=j ∧ σ.vars "choose.cols"=k+1 ∧
      Prefix ((table n k).take (i*(k+1)+j)) "choose.table" σ) entry
      (fun _ τ => τ.vars "choose.value"=i.choose j) 30 := by
  rintro σ ⟨hrow,hcol,hcols,hprefix⟩
  have hzero : 0<B := by omega
  have hone : 1<B := by omega
  have hiB : i<B := by omega
  have hjB : j<B := by omega
  have hkB : k+1<B := by omega
  by_cases hj0 : j=0
  · subst j
    run_vcg
    all_goals simp_all [Env.setVar]
  · by_cases hi0 : i=0
    · subst i
      have hchoose : Nat.choose 0 j=0 := Nat.choose_eq_zero_of_lt (by omega)
      run_vcg
      all_goals simp_all [Env.setVar]
    · have hjp : 0<j := by omega
      have hip : 0 < i := by omega
      have hrec : i.choose j=(i-1).choose (j-1)+(i-1).choose j := by
        obtain ⟨i',rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        obtain ⟨j',rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        simp [Nat.choose_succ_succ]
      have hlast : i*(k+1)+j<(table n k).length := by rw [table_length]; nlinarith only [hi,hj]
      have hidx0 : (i-1)*(k+1)+(j-1)< i*(k+1)+j := by
        have hsubi : i-1+1=i := by omega
        have hsubj : j-1+1=j := by omega
        nlinarith only [hsubi,hsubj]
      have hidx1 : (i-1)*(k+1)+j< i*(k+1)+j := by
        have hsubi : i-1+1=i := by omega
        nlinarith only [hsubi]
      have get (a b : ℕ) (ha : a≤n) (hb : b≤k) (hlt : a*(k+1)+b< i*(k+1)+j) :
          (σ.arrs "choose.table")[a*(k+1)+b]?=some (a.choose b) := by
        have hp := hprefix (a*(k+1)+b) (by rw [List.length_take]; omega)
        rw [List.getElem_take] at hp
        have hc := table_coordinate n k a b ha hb
        rw [List.getElem?_eq_getElem (hlt.trans hlast)] at hc
        exact hp.trans hc
      have hget0 := get (i-1) (j-1) (by omega) (by omega) hidx0
      have hget1 := get (i-1) j (by omega) hj hidx1
      have hroom0 : (i-1)*(k+1)+(j-1)<(σ.arrs "choose.table").length := by
        by_contra hh
        rw [List.getElem?_eq_none (by omega)] at hget0
        contradiction
      have hroom1 : (i-1)*(k+1)+j<(σ.arrs "choose.table").length := by
        by_contra hh
        rw [List.getElem?_eq_none (by omega)] at hget1
        contradiction
      have hc0 := hcoeff (i-1) (by omega) (j-1) (by omega)
      have hc1 := hcoeff (i-1) (by omega) j hj
      have hsum : (i-1).choose (j-1)+(i-1).choose j<B := hrec ▸ hcoeff i hi j hj
      have hdim : (table n k).length<B := by rw [table_length]; omega
      have hprev : (i-1)*(k+1)<B := by omega
      have hb0 : (i-1)*(k+1)+(j-1)<B := (hidx0.trans hlast).trans hdim
      have hb1 : (i-1)*(k+1)+j<B := (hidx1.trans hlast).trans hdim
      run_vcg
      all_goals simp_all [Env.setVar]

def Invariant (n k : ℕ) (σ : Env) : Prop :=
  σ.vars "choose.cols"=k+1 ∧ σ.vars "choose.length"=(table n k).length ∧
  σ.vars "choose.i"≤(table n k).length ∧ (table n k).length≤(σ.arrs "choose.table").length ∧
  Prefix ((table n k).take (σ.vars "choose.i")) "choose.table" σ

theorem step_spec (B n k : ℕ) (hB : (n+1)*(k+1)+n+k+3<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (fun σ => Invariant n k σ ∧ σ.vars "choose.i"<(table n k).length) step
      (fun σ τ => Invariant n k τ ∧ τ.vars "choose.i"=σ.vars "choose.i"+1) 50 := by
  rintro σ ⟨⟨hcols,hlen,hle,hroom,hprefix⟩,hlt⟩
  let q := σ.vars "choose.i"
  let i := q/(k+1)
  let j := q%(k+1)
  have hlen' := table_length n k
  have hq : q<(n+1)*(k+1) := by rwa [←hlen']
  have hi : i≤n := by
    have : q/(k+1)<n+1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hq
    omega
  have hj : j≤k := by have hh := Nat.mod_lt q (by omega : 0<k+1); omega
  have hqB : q<B := by omega
  have heq : i*(k+1)+j=q := by
    dsimp [i,j]
    simpa only [Nat.mul_comm] using Nat.div_add_mod q (k+1)
  obtain ⟨ν,r1,p1⟩ := coordinates_spec B q (k+1) (by omega) hqB (by omega) σ ⟨rfl,hcols⟩
  obtain ⟨μ,r2,p2⟩ := entry_spec B n k i j hi hj hB hcoeff ν
    ⟨p1.1,p1.2,(r1.frame_var "choose.cols" (by decide)).trans hcols,
      by rw [heq]; simpa only [Prefix,r1.frame_arr "choose.table" (by decide)] using hprefix⟩
  have r12 := r1.seq r2
  have hqμ : μ.vars "choose.i"=q := r12.frame_var "choose.i" (by decide)
  have htlen : ((table n k).take q).length=q := by rw [List.length_take]; omega
  have hvalue : (table n k)[q]=i.choose j := by
    have hc := table_coordinate n k i j hi hj
    rw [heq,List.getElem?_eq_getElem hlt] at hc
    exact Option.some.inj hc
  obtain ⟨τ,r3,p3⟩ := Lax455465Proofs.RamWordBuffer.append_spec B "choose.table" "choose.i"
    ((table n k).take q) (i.choose j) (.var "choose.value") (by omega) (by rw [htlen]; omega) μ
    ⟨by simpa only [Prefix,r12.frame_arr "choose.table" (by decide)] using hprefix,
      by rwa [htlen],by rw [htlen,Lax455465Proofs.RamFrames.run_array_length r12]; omega,
      by rw [evalB_var_iff]; exact ⟨p2.symm,p2 ▸ hcoeff i hi j hj⟩⟩
  have ht : τ.vars "choose.i"=q+1 := by simpa only [htlen] using p3.2
  have rr := r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "choose.cols" (by decide)).trans hcols,
    (rr.frame_var "choose.length" (by decide)).trans hlen,by rw [ht]; omega,?_,?_⟩
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem hlt,hvalue]
    exact p3.1

def metadata : Com := .seq (.assign "choose.cols" (.add (.var "choose.k") (.lit 1)))
  (.assign "choose.length" (.mul (.add (.var "choose.n") (.lit 1)) (.var "choose.cols")))

def command : Com := .seq metadata (.seq (.assign "choose.i" (.lit 0))
  (.while (.lt (.var "choose.i") (.var "choose.length")) step))

theorem command_spec (B n k : ℕ) (hB : (n+1)*(k+1)+n+k+3<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (fun σ => σ.vars "choose.n"=n ∧ σ.vars "choose.k"=k ∧
      (n+1)*(k+1)≤(σ.arrs "choose.table").length) command
      (fun _ τ => Prefix (table n k) "choose.table" τ ∧ τ.vars "choose.cols"=k+1)
      (54*(n+1)*(k+1)+16) := by
  have hl := table_length n k
  have hloop := Spec.forRangeZero "choose.i" "choose.length" (Invariant n k)
    (table n k).length 50 (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1)
    (step_spec B n k hB hcoeff)
  have hmeta : Spec B (fun σ => σ.vars "choose.n"=n ∧ σ.vars "choose.k"=k) metadata
      (fun _ τ => τ.vars "choose.cols"=k+1 ∧ τ.vars "choose.length"=(n+1)*(k+1)) 10 := by
    run_vcg
    all_goals simp_all [Env.setVar]
    all_goals omega
  rintro σ ⟨hn,hk,hroom⟩
  obtain ⟨ν,r1,p1⟩ := hmeta σ ⟨hn,hk⟩
  have hi : Invariant n k (ν.setVar "choose.i" 0) := by
    refine ⟨?_,?_,by simp,?_,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using p1.1
    · simpa only [vars_setVar,String.reduceEq,if_false,hl] using p1.2
    · rw [arrs_setVar,Lax455465Proofs.RamFrames.run_array_length r1,hl]
      exact hroom
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by rw [hl]; nlinarith),?_,p2.1.1⟩
  simpa only [p2.2,List.take_length] using p2.1.2.2.2.2

/-- The membership vector of the direct subset selection. -/
def bits : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | n+1, 0, q => 0::bits n 0 q
  | n+1, k+1, q => if q<n.choose (k+1) then 0::bits n (k+1) q
      else 1::bits n k (q-n.choose (k+1))

theorem bits_length (n k q : ℕ) : (bits n k q).length=n := by
  induction n generalizing k q with
  | zero => rfl
  | succ n ih =>
    cases k with
    | zero => simp [bits,ih]
    | succ k => simp only [bits]; split_ifs <;> simp [ih]

def decode {α : Type*} (xs : List α) (bs : List ℕ) : List α :=
  (xs.zip bs).filterMap fun p => if p.2=1 then some p.1 else none

theorem decode_bits {α : Type*} (xs : List α) (k q : ℕ) :
    decode xs (bits xs.length k q)=select k xs q := by
  induction xs generalizing k q with
  | nil => cases k <;> rfl
  | cons a xs ih =>
    cases k with
    | zero => simpa [decode,bits,select] using ih 0 q
    | succ k =>
      by_cases hq : q<xs.length.choose (k+1)
      · simpa [decode,bits,select,hq] using ih (k+1) q
      · simpa [decode,bits,select,hq] using congrArg (List.cons a) (ih k (q-xs.length.choose (k+1)))

def advance (remaining need rank : ℕ) : ℕ × ℕ × ℕ :=
  if need=0 then (0,need,rank)
  else if rank<(remaining-1).choose need then (0,need,rank)
  else (1,need-1,rank-(remaining-1).choose need)

theorem bits_step (remaining need rank : ℕ) (h : 0<remaining) :
    bits remaining need rank=(advance remaining need rank).1 ::
      bits (remaining-1) (advance remaining need rank).2.1 (advance remaining need rank).2.2 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
  cases need <;> simp [bits,advance]
  split_ifs <;> rfl

theorem advance_bounds (remaining need rank : ℕ) :
    (advance remaining need rank).1≤1 ∧ (advance remaining need rank).2.1≤need ∧
      (advance remaining need rank).2.2≤rank := by
  unfold advance
  split_ifs <;> simp

def subsetEntry : Com := .ite (.eq (.var "subset.need") (.lit 0))
  (.assign "subset.bit" (.lit 0))
  (.seq (.assign "subset.count" (.get "choose.table"
      (.add (.mul (.sub (.sub (.var "choose.n") (.var "subset.i")) (.lit 1)) (.var "choose.cols"))
        (.var "subset.need"))))
    (.ite (.lt (.var "subset.rank") (.var "subset.count")) (.assign "subset.bit" (.lit 0))
      (.seq (.assign "subset.bit" (.lit 1))
        (.seq (.assign "subset.rank" (.sub (.var "subset.rank") (.var "subset.count")))
          (.assign "subset.need" (.sub (.var "subset.need") (.lit 1)))))))

theorem subset_entry_spec (B n k i need rank : ℕ) (hi : i<n) (hneed : need≤k)
    (hB : (n+1)*(k+1)+n+k+3<B) (hrank : rank<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (fun σ => σ.vars "choose.n"=n ∧ σ.vars "choose.cols"=k+1 ∧
      σ.vars "subset.i"=i ∧ σ.vars "subset.need"=need ∧ σ.vars "subset.rank"=rank ∧
      Prefix (table n k) "choose.table" σ) subsetEntry
      (fun _ τ => τ.vars "subset.bit"=(advance (n-i) need rank).1 ∧
        τ.vars "subset.need"=(advance (n-i) need rank).2.1 ∧
        τ.vars "subset.rank"=(advance (n-i) need rank).2.2) 40 := by
  rintro σ ⟨hn,hcols,hiσ,hneedσ,hrankσ,hprefix⟩
  have hrow : n-i-1≤n := by omega
  have hidx : (n-i-1)*(k+1)+need<(table n k).length := by
    rw [table_length]
    nlinarith only [hrow,hneed]
  have hc := table_coordinate n k (n-i-1) need hrow hneed
  have hp := hprefix ((n-i-1)*(k+1)+need) hidx
  rw [List.getElem?_eq_getElem hidx] at hc
  have hget := hp.trans hc
  have hroom : (n-i-1)*(k+1)+need<(σ.arrs "choose.table").length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hget
    contradiction
  have htableB : (table n k).length<B := by rw [table_length]; omega
  have hidxB := hidx.trans htableB
  have hmul : (n-i-1)*(k+1)<B := by omega
  have hcB := hcoeff (n-i-1) hrow need hneed
  by_cases hneed0 : need=0
  · subst need
    run_vcg
    all_goals simp_all [Env.setVar,advance]
  · by_cases hsmall : rank<(n-i-1).choose need
    · have ha : advance (n-i) need rank=(0,need,rank) := by simp [advance,hneed0,hsmall]
      simp only [ha]
      run_vcg
      all_goals simp_all [Env.setVar,advance]
    · have ha : advance (n-i) need rank=(1,need-1,rank-(n-i-1).choose need) := by simp [advance,hneed0,hsmall]
      simp only [ha]
      run_vcg
      all_goals simp_all [Env.setVar,advance]
      all_goals omega

def subsetStep : Com := .seq subsetEntry
  (Lax455465Proofs.RamWordBuffer.append "subset.bits" "subset.i" (.var "subset.bit"))

def SubsetInvariant (n k rank : ℕ) (σ : Env) : Prop :=
  σ.vars "choose.n"=n ∧ σ.vars "choose.cols"=k+1 ∧
  Prefix (table n k) "choose.table" σ ∧ n≤(σ.arrs "subset.bits").length ∧
  σ.vars "subset.i"≤n ∧ σ.vars "subset.need"≤k ∧ σ.vars "subset.rank"≤rank ∧
  Prefix ((bits n k rank).take (σ.vars "subset.i")) "subset.bits" σ ∧
  (bits n k rank).drop (σ.vars "subset.i")=
    bits (n-σ.vars "subset.i") (σ.vars "subset.need") (σ.vars "subset.rank")

theorem subset_step_spec (B n k rank : ℕ) (hB : (n+1)*(k+1)+n+k+3<B) (hrank : rank<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (fun σ => SubsetInvariant n k rank σ ∧ σ.vars "subset.i"<n) subsetStep
      (fun σ τ => SubsetInvariant n k rank τ ∧ τ.vars "subset.i"=σ.vars "subset.i"+1) 50 := by
  rintro σ ⟨⟨hn,hcols,htable,hroom,hle,hneed,hq,hprefix,htail⟩,hlt⟩
  let i := σ.vars "subset.i"
  let need := σ.vars "subset.need"
  let q := σ.vars "subset.rank"
  let a := advance (n-i) need q
  let xs := bits n k rank
  have hlen : xs.length=n := bits_length _ _ _
  have hab := advance_bounds (n-i) need q
  have htail' : xs.drop i=a.1::bits (n-i-1) a.2.1 a.2.2 := by
    rw [htail,bits_step (n-i) need q (by omega)]
  have hval : xs[i]=a.1 := by
    have he := congrArg (fun ys : List ℕ => ys[0]?) htail'
    simp only [List.getElem?_drop,Nat.add_zero,List.getElem?_cons_zero] at he
    rw [List.getElem?_eq_getElem (by omega)] at he
    exact Option.some.inj he
  have hnext : xs.drop (i+1)=bits (n-(i+1)) a.2.1 a.2.2 := by
    rw [←List.drop_drop,htail']
    simp only [List.drop_succ_cons,List.drop_zero,Nat.sub_sub]
  obtain ⟨ν,r1,p1⟩ := subset_entry_spec B n k i need q hlt hneed hB (hq.trans_lt hrank) hcoeff σ
    ⟨hn,hcols,rfl,rfl,rfl,htable⟩
  have hiν : ν.vars "subset.i"=i := r1.frame_var "subset.i" (by decide)
  have htlen : (xs.take i).length=i := by rw [List.length_take,hlen]; omega
  have hbit : a.1<B := hab.1.trans_lt (by omega)
  obtain ⟨τ,r2,p2⟩ := Lax455465Proofs.RamWordBuffer.append_spec B "subset.bits" "subset.i"
    (xs.take i) a.1 (.var "subset.bit") (by omega) (by rw [htlen]; omega) ν
    ⟨by simpa only [Prefix,r1.frame_arr "subset.bits" (by decide)] using hprefix,
      by rwa [htlen],by rw [htlen,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨p1.1.symm,p1.1 ▸ hbit⟩⟩
  have ht : τ.vars "subset.i"=i+1 := by simpa only [htlen] using p2.2
  have htn : τ.vars "subset.need"=a.2.1 := (r2.frame_var "subset.need" (by decide)).trans p1.2.1
  have htq : τ.vars "subset.rank"=a.2.2 := (r2.frame_var "subset.rank" (by decide)).trans p1.2.2
  have rr := r1.seq r2
  refine ⟨τ,rr.mono (by simp [Expr.size]),?_,ht⟩
  refine ⟨(rr.frame_var "choose.n" (by decide)).trans hn,
    (rr.frame_var "choose.cols" (by decide)).trans hcols,?_,?_,by rw [ht]; omega,
    by rw [htn]; exact hab.2.1.trans hneed,by rw [htq]; exact hab.2.2.trans hq,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "choose.table" (by decide)] using htable
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem (by rw [bits_length]; exact hlt),hval]
    exact p2.1
  · rw [ht,htn,htq]
    exact hnext

def subsetCommand : Com := .seq (.assign "subset.i" (.lit 0))
  (.while (.lt (.var "subset.i") (.var "choose.n")) subsetStep)

theorem subset_command_spec (B n k rank : ℕ) (hB : (n+1)*(k+1)+n+k+3<B) (hrank : rank<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (fun σ => σ.vars "choose.n"=n ∧ σ.vars "choose.cols"=k+1 ∧
      σ.vars "subset.need"=k ∧ σ.vars "subset.rank"=rank ∧
      Prefix (table n k) "choose.table" σ ∧ n≤(σ.arrs "subset.bits").length) subsetCommand
      (fun _ τ => Prefix (bits n k rank) "subset.bits" τ) (54*n+6) := by
  have hloop := Spec.forRangeZero "subset.i" "choose.n" (SubsetInvariant n k rank) n 50
    (by omega) (fun _ h => h.2.2.2.2.1) (fun _ h => h.1) (subset_step_spec B n k rank hB hrank hcoeff)
  rintro σ ⟨hn,hcols,hneed,hq,htable,hroom⟩
  have hi : SubsetInvariant n k rank (σ.setVar "subset.i" 0) := by
    refine ⟨?_,?_,htable,hroom,by simp,?_,?_,?_,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hn
    · simpa only [vars_setVar,String.reduceEq,if_false] using hcols
    · simp only [vars_setVar,String.reduceEq,if_false,hneed,le_refl]
    · simp only [vars_setVar,String.reduceEq,if_false,hq,le_refl]
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
    · simp only [vars_setVar,String.reduceEq,if_true,if_false,List.drop_zero,Nat.sub_zero,hneed,hq]
  obtain ⟨τ,rr,p⟩ := hloop σ hi
  refine ⟨τ,rr,?_⟩
  have ht : (bits n k rank).take n=bits n k rank := List.take_of_length_le (by rw [bits_length])
  simpa only [p.2,ht] using p.1.2.2.2.2.2.2.2.1

theorem bits_binary (n k rank : ℕ) : ∀ b∈bits n k rank,b=0 ∨ b=1 := by
  induction n generalizing k rank with
  | zero => simp [bits]
  | succ n ih =>
    intro b hb
    cases k with
    | zero =>
      simp only [bits,List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact Or.inl rfl
      · exact ih _ _ b hb
    | succ k =>
      by_cases h : rank<n.choose (k+1)
      · simp only [bits,if_pos h,List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact Or.inl rfl
        · exact ih _ _ b hb
      · simp only [bits,if_neg h,List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact Or.inr rfl
        · exact ih _ _ b hb

theorem decode_get {α : Type*} (xs : List α) (bs : List ℕ) (hnd : xs.Nodup)
    (hlen : bs.length=xs.length) (i : ℕ) (hi : i<xs.length) :
    xs[i]∈decode xs bs ↔ bs[i]=1 := by
  constructor
  · intro h
    obtain ⟨p,hp,hval⟩ := List.mem_filterMap.mp h
    obtain ⟨j,hj,hpj⟩ := List.mem_iff_getElem.mp hp
    have hjx : j<xs.length := by simpa only [List.length_zip,hlen,Nat.min_self] using hj
    have hjb : j<bs.length := by omega
    rw [List.getElem_zip] at hpj
    subst p
    dsimp only at hval
    split_ifs at hval with hb
    · have hx : xs[j]=xs[i] := Option.some.inj hval
      have he : j=i := (List.Nodup.getElem_inj_iff hnd).mp hx
      subst j
      exact hb
  · intro hb
    apply List.mem_filterMap.mpr
    refine ⟨(xs[i],bs[i]),?_,?_⟩
    · have hz : i<(xs.zip bs).length := by simp only [List.length_zip,hlen,Nat.min_self]; exact hi
      have hh := List.getElem_mem hz
      simpa only [List.getElem_zip] using hh
    · simp [hb]

theorem bits_encoding (n k rank : ℕ) :
    bits n k rank=Lax263307.WeightedIndependentSet.encodeOutput
      (decode (List.finRange n) (bits n k rank)).toFinset := by
  let bs := bits n k rank
  let I := (decode (List.finRange n) bs).toFinset
  have hlen : bs.length=n := bits_length _ _ _
  apply List.ext_getElem
  · simpa [Lax263307.WeightedIndependentSet.encodeOutput] using hlen
  · intro i hi hi'
    have hin : i<n := by simpa only [bits_length] using hi
    have hxs : i<(List.finRange n).length := by simpa using hin
    have hd := decode_get (List.finRange n) bs (List.nodup_finRange n) (by simpa using hlen) i hxs
    simp only [List.getElem_finRange] at hd
    have hget : (Lax263307.WeightedIndependentSet.encodeOutput I)[i]=
        if (⟨i,hin⟩ : Fin n)∈I then 1 else 0 := List.getElem_ofFn hi'
    change bs[i]=(Lax263307.WeightedIndependentSet.encodeOutput I)[i]
    rw [hget]
    by_cases hb : bs[i]=1
    · have hm : (⟨i,hin⟩ : Fin n)∈I := List.mem_toFinset.mpr (hd.mpr hb)
      rw [if_pos hm]
      exact hb
    · have hz : bs[i]=0 := (bits_binary n k rank _ (List.getElem_mem hi)).resolve_right hb
      have hm : (⟨i,hin⟩ : Fin n)∉I := fun h => hb (hd.mp (List.mem_toFinset.mp h))
      rw [if_neg hm]
      exact hz

theorem candidate_coordinate (n k rank : ℕ) (hrank : rank<n.choose k) :
    (Lax263307.ExhaustiveTargets.candidates n k)[rank]?=
      some (decode (List.finRange n) (bits n k rank)).toFinset := by
  have hs := select_correct (List.finRange n) k rank (by simpa using hrank)
  rw [Lax263307.ExhaustiveTargets.candidates,List.getElem?_map,hs]
  simp only [Option.map_some]
  congr 2
  have hd := decode_bits (List.finRange n) k rank
  simpa only [List.length_finRange] using hd.symm

end Lax263307Proofs.NativeCombinations
