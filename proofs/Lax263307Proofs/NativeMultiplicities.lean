import Lax263307Proofs.NativeMaximum
import Lax455465Proofs.RamWordBuffer

set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeMultiplicities

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet

/-- The integer formula is valid for any positive-denominator fraction representations. -/
theorem quotient_copies (n wn wd en ed Wn Wd : ℕ) (hwd : 0<wd) (hed : 0<ed) (hWd : 0<Wd) :
    copyCount n wn wd en ed Wn Wd =
      ⌊((wn:ℚ)/wd) / (((en:ℚ)/ed)*((Wn:ℚ)/Wd)/(2*n))⌋₊ := by
  rw [copyCount, ← Rat.natFloor_natCast_div_natCast]
  congr 1
  push_cast
  have hd : (wd:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hwd)
  have he : (ed:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hed)
  have hD : (Wd:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt hWd)
  field_simp

def counts (n en ed Wn Wd : ℕ) (qs : List ℚ) : List ℕ :=
  qs.map fun q => copyCount n (clippedNumerator q) q.den en ed Wn Wd

def step : Com :=
  .seq (.assign "weight.position" (.add (.var "input.matrixLength") (.mul (.lit 3) (.var "weight.i"))))
  (.seq readWeight (.seq computeCopies
    (Lax455465Proofs.RamWordBuffer.append "copy.counts" "weight.i" (.var "copy.count"))))

def Invariant (front tail : List ℕ) (qs : List ℚ) (en ed Wn Wd : ℕ) (σ : Env) : Prop :=
  Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ ∧
  σ.vars "input.matrixLength"=front.length ∧ σ.vars "input.n"=qs.length ∧
  σ.vars "accuracy.n"=en ∧ σ.vars "accuracy.d"=ed ∧
  σ.vars "maximum.n"=Wn ∧ σ.vars "maximum.d"=Wd ∧
  σ.vars "weight.i"≤qs.length ∧ qs.length≤(σ.arrs "copy.counts").length ∧
  Prefix ((counts qs.length en ed Wn Wd qs).take (σ.vars "weight.i")) "copy.counts" σ


theorem product_bounds (B M n wn wd en ed Wn Wd : ℕ) (hM : 1≤M)
    (hB : 2*M^4+3<B) (hn : n≤M) (hwn : wn≤M) (hwd : wd≤M) (hen : en≤M)
    (hed : ed≤M) (hWn : Wn≤M) (hWd : Wd≤M) :
    2<B ∧ n<B ∧ wn<B ∧ wd<B ∧ en<B ∧ ed<B ∧ Wn<B ∧ Wd<B ∧
    2*n<B ∧ 2*n*wn<B ∧ 2*n*wn*ed<B ∧ 2*n*wn*ed*Wd<B ∧ wd*en<B ∧ wd*en*Wn<B := by
  have hp1 : M≤M^4 := by simpa using Nat.pow_le_pow_right hM (by omega : 1≤4)
  have hp2 : M^2≤M^4 := Nat.pow_le_pow_right hM (by omega)
  have hp3 : M^3≤M^4 := Nat.pow_le_pow_right hM (by omega)
  have hMB : M<B := by omega
  have h2M : 2*M^4<B := by omega
  have p1 : 2*n*wn≤2*M^2 := by calc
    _ ≤ 2*M*M := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hwn
    _ = _ := by ring
  have p2 : 2*n*wn*ed≤2*M^3 := by calc
    _ ≤ (2*M^2)*M := Nat.mul_le_mul p1 hed
    _ = _ := by ring
  have p3 : 2*n*wn*ed*Wd≤2*M^4 := by calc
    _ ≤ (2*M^3)*M := Nat.mul_le_mul p2 hWd
    _ = _ := by ring
  have p4 : wd*en≤M^2 := by simpa only [pow_two] using Nat.mul_le_mul hwd hen
  have p5 : wd*en*Wn≤M^3 := by calc
    _ ≤ M^2*M := Nat.mul_le_mul p4 hWn
    _ = _ := by ring
  exact ⟨by nlinarith only [hB,hM,hp1],hn.trans_lt hMB,hwn.trans_lt hMB,hwd.trans_lt hMB,
    hen.trans_lt hMB,hed.trans_lt hMB,hWn.trans_lt hMB,hWd.trans_lt hMB,
    by omega,by omega,by omega,p3.trans_lt h2M,by omega,by omega⟩

theorem step_spec (B M en ed Wn Wd : ℕ) (front tail : List ℕ) (qs : List ℚ)
    (hM : 1≤M) (hB : 2*M^4+3<B) (hn : qs.length≤M)
    (hen : en≤M) (hed : ed≤M) (hWn : Wn≤M) (hWd : Wd≤M)
    (hlen : front.length+3*qs.length+3<B)
    (hwords : ∀ q∈qs,q.num.natAbs≤M ∧ q.den≤M) :
    Spec B (fun σ => Invariant front tail qs en ed Wn Wd σ ∧ σ.vars "weight.i"<qs.length)
      step (fun σ τ => Invariant front tail qs en ed Wn Wd τ ∧ τ.vars "weight.i"=σ.vars "weight.i"+1) 54 := by
  have hMB : M<B := by
    have hp : M≤M^4 := by simpa using Nat.pow_le_pow_right hM (by omega : 1≤4)
    omega
  rintro σ ⟨⟨hp,hbase,hnσ,henσ,hedσ,hWnσ,hWdσ,hi,hroom,hprefix⟩,hlt⟩
  let i := σ.vars "weight.i"
  have hq := hwords qs[i] (List.getElem_mem hlt)
  have hc : clippedNumerator qs[i]≤M := by unfold clippedNumerator; split_ifs <;> omega
  have hb := product_bounds B M qs.length (clippedNumerator qs[i]) qs[i].den en ed Wn Wd
    hM hB hn hc hq.2 hen hed hWn hWd
  rcases hb with ⟨htwo,horder,hnum,hden,henB,hedB,hmaxn,hmaxd,hprod0,hprod1,hprod2,hprod3,hprod4,hprod5⟩
  have hpos : front.length+3*i<B := by omega
  have hiB : i<B := by omega
  have hfront : front.length<B := by omega
  have h3 : 3<B := by omega
  have h3i : 3*i<B := by omega
  have hpstep : Spec B (fun σ => σ.vars "input.matrixLength"=front.length ∧ σ.vars "weight.i"=i)
      (.assign "weight.position" (.add (.var "input.matrixLength") (.mul (.lit 3) (.var "weight.i"))))
      (fun _ τ => τ.vars "weight.position"=front.length+3*i) 6 := by
    run_vcg
    all_goals simp_all [Env.setVar]
  obtain ⟨ν,r1,p1⟩ := hpstep σ ⟨hbase,rfl⟩
  obtain ⟨μ,r2,p2⟩ := read_weight_from_prefix_spec B front tail qs i hlt (by omega) htwo
    (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) ν
    ⟨by simpa only [Prefix,r1.frame_arr "input.data" (by decide)] using hp,p1⟩
  have rr := r1.seq r2
  have hcalc := compute_copies_spec B qs.length (clippedNumerator qs[i]) qs[i].den en ed Wn Wd
    htwo horder hnum hden henB hedB hmaxn hmaxd hprod0 hprod1 hprod2 hprod3 hprod4 hprod5
  obtain ⟨ξ,r3,p3⟩ := hcalc μ ⟨(rr.frame_var "input.n" (by decide)).trans hnσ,p2.1,p2.2,
    (rr.frame_var "accuracy.n" (by decide)).trans henσ,(rr.frame_var "accuracy.d" (by decide)).trans hedσ,
    (rr.frame_var "maximum.n" (by decide)).trans hWnσ,(rr.frame_var "maximum.d" (by decide)).trans hWdσ⟩
  let xs := counts qs.length en ed Wn Wd qs
  let count := copyCount qs.length (clippedNumerator qs[i]) qs[i].den en ed Wn Wd
  have hxs : xs.length=qs.length := List.length_map _
  have hxsi : (xs.take i).length=i := by simp only [List.length_take,hxs]; omega
  have hcount : count<B := (Nat.div_le_self _ _).trans_lt hprod3
  have r123 := r1.seq (r2.seq r3)
  have hiξ : ξ.vars "weight.i"=i := r123.frame_var "weight.i" (by decide)
  have hprefixξ : Prefix (xs.take i) "copy.counts" ξ := by
    simpa only [Prefix,r123.frame_arr "copy.counts" (by decide)] using hprefix
  have hroomξ : i<(ξ.arrs "copy.counts").length := by
    rw [Lax455465Proofs.RamFrames.run_array_length r123]
    omega
  obtain ⟨τ,r4,p4⟩ := Lax455465Proofs.RamWordBuffer.append_spec B "copy.counts" "weight.i"
    (xs.take i) count (.var "copy.count") (by omega) (by rw [hxsi]; omega) ξ
    ⟨hprefixξ,by rwa [hxsi],by rwa [hxsi],by rw [evalB_var_iff]; exact ⟨p3.symm,p3 ▸ hcount⟩⟩
  have hnext : xs.take i++[count]=xs.take (i+1) := by
    rw [List.take_succ_eq_append_getElem (by omega : i<xs.length)]
    simp only [xs,counts,List.getElem_map]
    rfl
  have hti : τ.vars "weight.i"=i+1 := by simpa only [hxsi] using p4.2
  have rtotal := r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rtotal.mono (by simp only [Expr.size]; omega),?_,hti⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,by omega,?_,?_⟩
  · simpa only [Prefix,rtotal.frame_arr "input.data" (by decide)] using hp
  · exact (rtotal.frame_var "input.matrixLength" (by decide)).trans hbase
  · exact (rtotal.frame_var "input.n" (by decide)).trans hnσ
  · exact (rtotal.frame_var "accuracy.n" (by decide)).trans henσ
  · exact (rtotal.frame_var "accuracy.d" (by decide)).trans hedσ
  · exact (rtotal.frame_var "maximum.n" (by decide)).trans hWnσ
  · exact (rtotal.frame_var "maximum.d" (by decide)).trans hWdσ
  · rwa [Lax455465Proofs.RamFrames.run_array_length rtotal]
  · rw [hti]
    simpa only [hnext] using p4.1


def command : Com := .seq (.assign "weight.i" (.lit 0))
  (.while (.lt (.var "weight.i") (.var "input.n")) step)

theorem command_spec (B M en ed Wn Wd : ℕ) (front tail : List ℕ) (qs : List ℚ)
    (hM : 1≤M) (hB : 2*M^4+3<B) (hn : qs.length≤M)
    (hen : en≤M) (hed : ed≤M) (hWn : Wn≤M) (hWd : Wd≤M)
    (hlen : front.length+3*qs.length+3<B)
    (hwords : ∀ q∈qs,q.num.natAbs≤M ∧ q.den≤M) :
    Spec B (fun σ => Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ ∧
      σ.vars "input.matrixLength"=front.length ∧ σ.vars "input.n"=qs.length ∧
      σ.vars "accuracy.n"=en ∧ σ.vars "accuracy.d"=ed ∧
      σ.vars "maximum.n"=Wn ∧ σ.vars "maximum.d"=Wd ∧ qs.length≤(σ.arrs "copy.counts").length)
      command (fun _ τ => Prefix (counts qs.length en ed Wn Wd qs) "copy.counts" τ)
      (58*qs.length+6) := by
  have hlen' : qs.length<B := by omega
  have hstep := step_spec B M en ed Wn Wd front tail qs hM hB hn hen hed hWn hWd hlen hwords
  have hloop := Spec.forRangeZero "weight.i" "input.n" (Invariant front tail qs en ed Wn Wd)
    qs.length 54 hlen' (fun _ h => h.2.2.2.2.2.2.2.1) (fun _ h => h.2.2.1) hstep
  rintro σ ⟨hp,hbase,hnσ,henσ,hedσ,hWnσ,hWdσ,hroom⟩
  have hi : Invariant front tail qs en ed Wn Wd (σ.setVar "weight.i" 0) := by
    refine ⟨hp,?_,?_,?_,?_,?_,?_,by simp, hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hbase
    · simpa only [vars_setVar,String.reduceEq,if_false] using hnσ
    · simpa only [vars_setVar,String.reduceEq,if_false] using henσ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hedσ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hWnσ
    · simpa only [vars_setVar,String.reduceEq,if_false] using hWdσ
    · simp only [vars_setVar,if_true,List.take_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,rr,hpost⟩ := hloop σ hi
  refine ⟨τ,rr,?_⟩
  have hx := hpost.1.2.2.2.2.2.2.2.2.2
  rw [hpost.2] at hx
  have heq : (counts qs.length en ed Wn Wd qs).take qs.length = counts qs.length en ed Wn Wd qs :=
    List.take_of_length_le (by simp [counts])
  simpa only [heq] using hx

theorem counts_correct {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) (hε : 0<ε) :
    let a := Lax263307Proofs.NativeMaximum.maximum (List.ofFn w)
    counts n ε.num.natAbs ε.den a.1 a.2 (List.ofFn w) =
      List.ofFn (Lax263307.WeightRounding.copies (fun v => max (w v) 0) ε) := by
  intro a
  have hpositive : 0<a.2 := by
    -- Only positivity is needed; it follows directly through each selected pair.
    have hp (qs : List ℚ) (b : ℕ×ℕ) (hb : 0<b.2) :
        0<(qs.foldl Lax263307Proofs.NativeMaximum.advance b).2 := by
      induction qs generalizing b with
      | nil => exact hb
      | cons q qs ih => exact ih _ (Lax263307Proofs.NativeMaximum.advance_positive b q hb)
    exact hp _ (0,1) (by omega)
  have henum : (ε.num.natAbs:ℚ)=(ε.num:ℚ) := by
    have he : (ε.num.natAbs:ℤ)=ε.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hε.le)
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) he
  simp only [counts,List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  dsimp only [Function.comp_apply]
  rw [quotient_copies _ _ _ _ _ _ _ (w v).den_pos ε.den_pos hpositive,clipped_value,henum,ε.num_div_den]
  have hmax := Lax263307Proofs.NativeMaximum.maximum_value w
  change (a.1:ℚ)/a.2 = _ at hmax
  rw [hmax]
  rfl


def readAccuracy : Com :=
  .seq (.assign "weight.position" (.add (.var "input.matrixLength") (.var "input.weightLength")))
  (.seq readWeight
    (.seq (.assign "accuracy.n" (.var "weight.n")) (.assign "accuracy.d" (.var "weight.d"))))

theorem read_accuracy_spec (B : ℕ) (front : List ℕ) (qs : List ℚ) (ε : ℚ) (hε : 0<ε)
    (hsize : front.length+3*qs.length+3<B) (hnum : ε.num.natAbs<B) (hden : ε.den<B) :
    Spec B (fun σ => Prefix (front++qs.flatMap encodeRational++encodeRational ε) "input.data" σ ∧
      σ.vars "input.matrixLength"=front.length ∧ σ.vars "input.weightLength"=3*qs.length)
      readAccuracy (fun _ τ => τ.vars "accuracy.n"=ε.num.natAbs ∧ τ.vars "accuracy.d"=ε.den) 32 := by
  let pos := front.length+3*qs.length
  have hpos : pos<B := by omega
  have hfront : front.length<B := by omega
  have hw : 3*qs.length<B := by omega
  have h2 : 2<B := by omega
  have hclip : clippedNumerator ε=ε.num.natAbs := by
    unfold clippedNumerator
    rw [if_neg (not_lt.mpr (Rat.num_nonneg.mpr hε.le))]
  rintro σ ⟨hp,hbase,hwlen⟩
  let ν := σ.setVar "weight.position" pos
  have r1 : Run B (.assign "weight.position" (.add (.var "input.matrixLength") (.var "input.weightLength"))) σ ν 4 := by
    apply Run.assign
    apply evalB_bin (op:=.add)
    · rw [evalB_var_iff]; exact ⟨hbase.symm,hbase ▸ hfront⟩
    · rw [evalB_var_iff]; exact ⟨hwlen.symm,hwlen ▸ hw⟩
    · exact hpos
  have hencoded : (front++qs.flatMap encodeRational++encodeRational ε).length=pos+3 := by
    rw [List.length_append,List.length_append,encoded_length]
    simp only [encodeRational,List.length_cons,List.length_nil]
    rfl
  have hget (j : ℕ) (hj : j<3) : (ν.arrs "input.data")[pos+j]?=(encodeRational ε)[j]? := by
    have hidx : pos+j<(front++qs.flatMap encodeRational++encodeRational ε).length := by omega
    have hh := hp (pos+j) hidx
    rw [← List.getElem?_eq_getElem hidx] at hh
    change (σ.arrs "input.data")[pos+j]?=(encodeRational ε)[j]?
    rw [hh,List.getElem?_append_right (by rw [List.length_append,encoded_length]; dsimp [pos]; omega)]
    congr 1
    rw [List.length_append,encoded_length]
    dsimp only [pos]
    omega
  obtain ⟨μ,r2,p2⟩ := read_weight_spec B pos ε (by omega) h2 hnum hden ν
    ⟨by simp [ν],by simpa [encodeRational] using hget 0 (by omega),
      by simpa [encodeRational] using hget 1 (by omega),
      by simpa [encodeRational] using hget 2 (by omega)⟩
  have hnμ : μ.vars "weight.n"=ε.num.natAbs := p2.1.trans hclip
  let ξ := μ.setVar "accuracy.n" ε.num.natAbs
  have r3 : Run B (.assign "accuracy.n" (.var "weight.n")) μ ξ 2 := Run.assign (by
    rw [evalB_var_iff]; exact ⟨hnμ.symm,hnμ ▸ hnum⟩)
  let τ := ξ.setVar "accuracy.d" ε.den
  have hdξ : ξ.vars "weight.d"=ε.den := (r3.frame_var "weight.d" (by decide)).trans p2.2
  have r4 : Run B (.assign "accuracy.d" (.var "weight.d")) ξ τ 2 := Run.assign (by
    rw [evalB_var_iff]; exact ⟨hdξ.symm,hdξ ▸ hden⟩)
  exact ⟨τ,r1.seq (r2.seq (r3.seq r4)),by simp [τ,ξ],by simp [τ]⟩

end Lax263307Proofs.NativeMultiplicities
