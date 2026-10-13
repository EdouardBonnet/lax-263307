import Lax263307.WeightRounding
import Lax455465Proofs.RamInputCopy
import Lax455465Proofs.RamVirtualState
import Lax109476Proofs.RamAutomaticLayout
import Mathlib.Tactic

namespace Lax263307Proofs.NativeFrontend

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307.WeightedIndependentSet

def tailInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (ε : ℚ) : List ℕ :=
  (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten ++ encodeParameters w ε

theorem tail_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (ε : ℚ) : (tailInput G w ε).length = n*n + 3*n + 3 := by
  simp [tailInput, encodeParameters, encodeRational, List.length_flatten, List.length_flatMap,
    List.sum_ofFn, Finset.sum_const, Nat.mul_comm, Nat.add_assoc]

def metadata : Com :=
  .seq (.assign "input.matrixLength" (.mul (.var "input.n") (.var "input.n")))
  (.seq (.assign "input.weightLength" (.mul (.lit 3) (.var "input.n")))
    (.assign "input.length" (.add (.add (.var "input.matrixLength") (.var "input.weightLength")) (.lit 3))))

def readInput : Com := .seq (.read "input.n") (.seq metadata
  (.seq (.assign "input.i" (.lit 0))
    (.while (.lt (.var "input.i") (.var "input.length")) RamInputCopy.copyStep)))

theorem metadata_spec (B n : ℕ) (hsize : n*n+3*n+3 < B) :
    Spec B (fun σ => σ.vars "input.n"=n) metadata
      (fun _ τ => τ.vars "input.n"=n ∧ τ.vars "input.matrixLength"=n*n ∧
        τ.vars "input.weightLength"=3*n ∧ τ.vars "input.length"=n*n+3*n+3) 20 := by
  have hn : n < B := by nlinarith only [hsize]
  have hnn : n*n < B := by omega
  have h3n : 3*n < B := by omega
  have hadd : n*n+3*n < B := by omega
  have h3 : 3 < B := by omega
  rintro σ hσ
  run_vcg
  all_goals simp_all [Env.setVar]

theorem read_input_spec (B n : ℕ) (xs : List ℕ) (hsize : n*n+3*n+3 < B)
    (hlen : xs.length=n*n+3*n+3) (hwords : ∀ x∈xs,x<B) :
    Spec B (fun σ => σ.inp=n::xs ∧ xs.length≤(σ.arrs "input.data").length) readInput
      (fun _ τ => τ.vars "input.n"=n ∧ τ.vars "input.matrixLength"=n*n ∧
        τ.vars "input.weightLength"=3*n ∧ τ.vars "input.length"=xs.length ∧
        τ.inp=[] ∧ Prefix xs "input.data" τ) (12*xs.length+30) := by
  have hn : n<B := by nlinarith only [hsize]
  have h1 : 1<B := by omega
  have hx : xs.length<B := by omega
  have hloop := Spec.forRangeZero "input.i" "input.length" (RamInputCopy.Invariant xs) xs.length 8 hx
    (fun _ h => h.2.1) (fun _ h => h.1) (RamInputCopy.copyStep_spec B xs h1 hx hwords)
  rintro σ ⟨hinp,hroom⟩
  let ν := {σ.setVar "input.n" n with inp := xs}
  have rr : Run B (.read "input.n") σ ν 1 := Run.read hinp
  obtain ⟨μ,rm,hm⟩ := metadata_spec B n hsize ν (by simp [ν])
  have hinpμ : μ.inp=xs := (rm.frame_inp (by decide)).trans (by simp [ν])
  have hroomμ : xs.length≤(μ.arrs "input.data").length := by
    rw [rm.frame_arr "input.data" (by decide)]
    exact hroom
  have hi : RamInputCopy.Invariant xs (μ.setVar "input.i" 0) := by
    refine ⟨?_,by simp,?_,hroomμ,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false,hlen] using hm.2.2.2
    · simpa only [inp_setVar,vars_setVar,if_true,List.drop_zero] using hinpμ
    · intro j hj
      simp only [vars_setVar,if_true] at hj
      omega
  obtain ⟨τ,rl,hl⟩ := hloop μ hi
  refine ⟨τ,(rr.seq (rm.seq rl)).mono (by omega),?_,?_,?_,hl.1.1,?_,?_⟩
  · exact (rl.frame_var "input.n" (by decide)).trans hm.1
  · exact (rl.frame_var "input.matrixLength" (by decide)).trans hm.2.1
  · exact (rl.frame_var "input.weightLength" (by decide)).trans hm.2.2.1
  · simpa only [hl.2,List.drop_length] using hl.1.2.2.1
  · intro j hj
    have hh := hl.1.2.2.2.2 j (by simpa only [hl.2] using hj)
    simpa only [List.getElem?_eq_getElem hj] using hh


/-- Exact copy count using only natural products and division. -/
def copyCount (n wn wd en ed Wn Wd : ℕ) : ℕ :=
  (2*n*wn*ed*Wd) / (wd*en*Wn)

theorem copy_count_eq (n : ℕ) (q ε W : ℚ) (hq : 0 ≤ q) (hε : 0 ≤ ε) (hW : 0 ≤ W) :
    copyCount n q.num.natAbs q.den ε.num.natAbs ε.den W.num.natAbs W.den =
      ⌊q / (ε*W/(2*n))⌋₊ := by
  have hqnum : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
    have he : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq)
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he
  have henum : (ε.num.natAbs : ℚ) = (ε.num : ℚ) := by
    have he : (ε.num.natAbs : ℤ) = ε.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hε)
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he
  have hWnum : (W.num.natAbs : ℚ) = (W.num : ℚ) := by
    have he : (W.num.natAbs : ℤ) = W.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hW)
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he
  rw [copyCount, ← Rat.natFloor_natCast_div_natCast]
  congr 1
  push_cast
  rw [hqnum, henum, hWnum]
  have hqrep : (q.num:ℚ) = q*q.den := (div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den
  have herep : (ε.num:ℚ) = ε*ε.den := (div_eq_iff (by exact_mod_cast ε.den_ne_zero)).mp ε.num_div_den
  have hWrep : (W.num:ℚ) = W*W.den := (div_eq_iff (by exact_mod_cast W.den_ne_zero)).mp W.num_div_den
  rw [hqrep,herep,hWrep]
  field_simp

def computeCopies : Com := .assign "copy.count"
  (.div (.mul (.mul (.mul (.mul (.lit 2) (.var "input.n")) (.var "weight.n"))
    (.var "accuracy.d")) (.var "maximum.d"))
    (.mul (.mul (.var "weight.d") (.var "accuracy.n")) (.var "maximum.n")))

theorem compute_copies_spec (B n wn wd en ed Wn Wd : ℕ)
    (h2 : 2<B) (hn : n<B) (hwn : wn<B) (hwd : wd<B) (hen : en<B) (hed : ed<B)
    (hWn : Wn<B) (hWd : Wd<B)
    (h0 : 2*n<B) (h1 : 2*n*wn<B) (h2' : 2*n*wn*ed<B) (h3 : 2*n*wn*ed*Wd<B)
    (h4 : wd*en<B) (h5 : wd*en*Wn<B) :
    Spec B (fun σ => σ.vars "input.n"=n ∧ σ.vars "weight.n"=wn ∧ σ.vars "weight.d"=wd ∧
      σ.vars "accuracy.n"=en ∧ σ.vars "accuracy.d"=ed ∧ σ.vars "maximum.n"=Wn ∧ σ.vars "maximum.d"=Wd)
      computeCopies (fun _ τ => τ.vars "copy.count"=copyCount n wn wd en ed Wn Wd) 16 := by
  have hq : copyCount n wn wd en ed Wn Wd<B := (Nat.div_le_self _ _).trans_lt h3
  rintro σ ⟨hσn,hσwn,hσwd,hσen,hσed,hσWn,hσWd⟩
  run_vcg
  all_goals simp_all [copyCount,Env.setVar]


def maximumPair (an ad bn bd : ℕ) : ℕ × ℕ := if an*bd < bn*ad then (bn,bd) else (an,ad)

theorem maximum_pair_value (an ad bn bd : ℕ) (had : 0<ad) (hbd : 0<bd) :
    ((maximumPair an ad bn bd).1 : ℚ) / (maximumPair an ad bn bd).2 =
      max ((an:ℚ)/ad) ((bn:ℚ)/bd) := by
  have hd : (0:ℚ)<ad := Nat.cast_pos.mpr had
  have he : (0:ℚ)<bd := Nat.cast_pos.mpr hbd
  have heq : an*bd < bn*ad ↔ (an:ℚ)/ad < (bn:ℚ)/bd := by
    rw [div_lt_div_iff₀ hd he]
    norm_cast
  unfold maximumPair
  split_ifs with h
  · exact (max_eq_right (heq.mp h).le).symm
  · exact (max_eq_left (le_of_not_gt (mt heq.mpr h))).symm

def updateMaximum : Com :=
  .ite (.lt (.mul (.var "maximum.n") (.var "weight.d"))
    (.mul (.var "weight.n") (.var "maximum.d")))
    (.seq (.assign "maximum.n" (.var "weight.n")) (.assign "maximum.d" (.var "weight.d"))) .skip

theorem update_maximum_spec (B an ad bn bd : ℕ) (han : an<B) (had : ad<B) (hbn : bn<B)
    (hbd : bd<B) (hleft : an*bd<B) (hright : bn*ad<B) :
    Spec B (fun σ => σ.vars "maximum.n"=an ∧ σ.vars "maximum.d"=ad ∧
      σ.vars "weight.n"=bn ∧ σ.vars "weight.d"=bd) updateMaximum
      (fun _ τ => τ.vars "maximum.n"=(maximumPair an ad bn bd).1 ∧
        τ.vars "maximum.d"=(maximumPair an ad bn bd).2) 12 := by
  rintro σ ⟨hσan,hσad,hσbn,hσbd⟩
  run_vcg
  all_goals simp_all [maximumPair,Env.setVar] <;> split_ifs <;> simp_all <;> omega


def clippedNumerator (q : ℚ) : ℕ := if q.num < 0 then 0 else q.num.natAbs

theorem clipped_value (q : ℚ) : (clippedNumerator q : ℚ) / q.den = max q 0 := by
  unfold clippedNumerator
  split_ifs with h
  · have hq : q < 0 := Rat.num_neg.mp h
    simp [max_eq_right hq.le]
  · have hn : 0 ≤ q.num := le_of_not_gt h
    have hq : 0 ≤ q := Rat.num_nonneg.mp hn
    rw [max_eq_left hq]
    have hcast : (q.num.natAbs : ℚ) = (q.num : ℚ) := by
      have he : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hn
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) he
    rw [hcast, q.num_div_den]

def readWeight : Com :=
  .seq (.assign "weight.s" (.get "input.data" (.var "weight.position")))
  (.seq (.assign "weight.n" (.get "input.data" (.add (.var "weight.position") (.lit 1))))
  (.seq (.assign "weight.d" (.get "input.data" (.add (.var "weight.position") (.lit 2))))
    (.ite (.eq (.var "weight.s") (.lit 1)) (.assign "weight.n" (.lit 0)) .skip)))

theorem read_weight_spec (B pos : ℕ) (q : ℚ) (hp : pos+2<B) (h2 : 2<B)
    (hn : q.num.natAbs<B) (hd : q.den<B) :
    Spec B (fun σ => σ.vars "weight.position"=pos ∧
      (σ.arrs "input.data")[pos]?=some (if q.num<0 then 1 else 0) ∧
      (σ.arrs "input.data")[pos+1]?=some q.num.natAbs ∧
      (σ.arrs "input.data")[pos+2]?=some q.den) readWeight
      (fun _ τ => τ.vars "weight.n"=clippedNumerator q ∧ τ.vars "weight.d"=q.den) 24 := by
  have hsign : (if q.num<0 then 1 else 0)<B := by split_ifs <;> omega
  rintro σ ⟨hpos,hs,hn',hd'⟩
  have hroom : pos+2 < (σ.arrs "input.data").length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hd'
    contradiction
  run_vcg
  all_goals simp_all [clippedNumerator,Env.setVar]


theorem encoded_coordinate (qs : List ℚ) (i j : ℕ) (hi : i<qs.length) (hj : j<3) :
    (qs.flatMap encodeRational)[3*i+j]? = (encodeRational qs[i])[j]? := by
  induction qs generalizing i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons,Nat.mul_zero,Nat.zero_add,List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simpa [encodeRational] using hj)]
    | succ i =>
      have hi' : i<qs.length := by simpa using hi
      simp only [List.flatMap_cons,List.getElem_cons_succ]
      rw [List.getElem?_append_right (by simp [encodeRational]; omega)]
      have hidx : 3*(i+1)+j-(encodeRational q).length=3*i+j := by simp [encodeRational]; omega
      rw [hidx]
      exact ih i hi'

theorem encoded_length (qs : List ℚ) : (qs.flatMap encodeRational).length=3*qs.length := by
  induction qs with
  | nil => simp
  | cons q qs ih => simp [encodeRational,ih,Nat.mul_add,Nat.add_comm]; omega

theorem prefixed_coordinate (front tail : List ℕ) (qs : List ℚ) (i j : ℕ)
    (hi : i<qs.length) (hj : j<3) :
    (front++qs.flatMap encodeRational++tail)[front.length+3*i+j]?=(encodeRational qs[i])[j]? := by
  rw [List.append_assoc,List.getElem?_append_right (by omega)]
  have hidx : front.length+3*i+j-front.length=3*i+j := by omega
  rw [hidx,List.getElem?_append_left (by rw [encoded_length]; omega)]
  exact encoded_coordinate qs i j hi hj


theorem read_weight_from_prefix_spec (B : ℕ) (front tail : List ℕ) (qs : List ℚ)
    (i : ℕ) (hi : i<qs.length) (hsize : front.length+3*qs.length+1<B)
    (h2 : 2<B) (hn : qs[i].num.natAbs<B) (hd : qs[i].den<B) :
    Spec B (fun σ => Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ ∧
      σ.vars "weight.position"=front.length+3*i) readWeight
      (fun _ τ => τ.vars "weight.n"=clippedNumerator qs[i] ∧ τ.vars "weight.d"=qs[i].den) 24 := by
  rintro σ ⟨hp,hpos⟩
  apply read_weight_spec B (front.length+3*i) qs[i] (by omega) h2 hn hd σ
  refine ⟨hpos,?_,?_,?_⟩
  all_goals
    have hget (j : ℕ) (hj : j<3) :
        (σ.arrs "input.data")[front.length+3*i+j]?=(encodeRational qs[i])[j]? := by
      have hidx : front.length+3*i+j < (front++qs.flatMap encodeRational++tail).length := by
        rw [List.length_append,List.length_append,encoded_length]
        omega
      have hh := hp (front.length+3*i+j) hidx
      rw [← List.getElem?_eq_getElem hidx] at hh
      exact hh.trans (prefixed_coordinate front tail qs i j hi hj)
  · simpa only [Nat.add_zero,encodeRational,List.getElem?_cons_zero] using hget 0 (by omega)
  · simpa only [encodeRational,List.getElem?_cons_succ,List.getElem?_cons_zero] using hget 1 (by omega)
  · simpa only [encodeRational,List.getElem?_cons_succ,List.getElem?_cons_zero] using hget 2 (by omega)

def maximumStep : Com :=
  .seq (.assign "weight.position" (.add (.var "input.matrixLength") (.mul (.lit 3) (.var "weight.i"))))
  (.seq readWeight (.seq updateMaximum (.assign "weight.i" (.add (.var "weight.i") (.lit 1)))))

theorem maximum_step_spec (B an ad : ℕ) (front tail : List ℕ) (qs : List ℚ)
    (i : ℕ) (hi : i<qs.length) (hsize : front.length+3*qs.length+3<B)
    (han : an<B) (had : ad<B) (hn : qs[i].num.natAbs<B) (hd : qs[i].den<B)
    (hleft : an*qs[i].den<B) (hright : clippedNumerator qs[i]*ad<B) :
    Spec B (fun σ => Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ ∧
      σ.vars "input.matrixLength"=front.length ∧ σ.vars "weight.i"=i ∧
      σ.vars "maximum.n"=an ∧ σ.vars "maximum.d"=ad) maximumStep
      (fun _ τ => τ.vars "weight.i"=i+1 ∧
        τ.vars "maximum.n"=(maximumPair an ad (clippedNumerator qs[i]) qs[i].den).1 ∧
        τ.vars "maximum.d"=(maximumPair an ad (clippedNumerator qs[i]) qs[i].den).2) 48 := by
  have hiB : i<B := by omega
  have hfront : front.length<B := by omega
  have h3 : 3<B := by omega
  have h3i : 3*i<B := by omega
  have hpos : front.length+3*i<B := by omega
  have hclip : clippedNumerator qs[i]<B := by unfold clippedNumerator; split_ifs <;> omega
  have hread := read_weight_from_prefix_spec B front tail qs i hi (by omega) (by omega) hn hd
  have hmax := update_maximum_spec B an ad (clippedNumerator qs[i]) qs[i].den han had hclip hd hleft hright
  rintro σ ⟨hp,hbase,hiσ,hanσ,hadσ⟩
  have hpstep : Spec B (fun σ => σ.vars "input.matrixLength"=front.length ∧ σ.vars "weight.i"=i)
      (.assign "weight.position" (.add (.var "input.matrixLength") (.mul (.lit 3) (.var "weight.i"))))
      (fun _ τ => τ.vars "weight.position"=front.length+3*i) 6 := by
    run_vcg
    all_goals simp_all [Env.setVar]
  obtain ⟨ν,r1,p1⟩ := hpstep σ ⟨hbase,hiσ⟩
  obtain ⟨μ,r2,p2⟩ := hread ν ⟨by simpa only [Prefix,r1.frame_arr "input.data" (by decide)] using hp,p1⟩
  have ra := r1.seq r2
  have ha : μ.vars "maximum.n"=an := (ra.frame_var "maximum.n" (by decide)).trans hanσ
  have hd' : μ.vars "maximum.d"=ad := (ra.frame_var "maximum.d" (by decide)).trans hadσ
  obtain ⟨ξ,r3,p3⟩ := hmax μ ⟨ha,hd',p2.1,p2.2⟩
  have hb := ra.seq r3
  have hiξ : ξ.vars "weight.i"=i := (hb.frame_var "weight.i" (by decide)).trans hiσ
  let τ := ξ.setVar "weight.i" (i+1)
  have r4 : Run B (.assign "weight.i" (.add (.var "weight.i") (.lit 1))) ξ τ 4 := by
    apply Run.assign
    apply evalB_bin (op:=.add)
    · rw [evalB_var_iff]; exact ⟨hiξ.symm,hiξ ▸ hiB⟩
    · exact evalB_lit (by omega)
    · dsimp [Bop.apply]; omega
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),by simp [τ],?_,?_⟩
  · simpa only [τ,vars_setVar,String.reduceEq,if_false] using p3.1
  · simpa only [τ,vars_setVar,String.reduceEq,if_false] using p3.2

end Lax263307Proofs.NativeFrontend
