import Lax263307Proofs.NativeFrontend

set_option maxHeartbeats 800000

namespace Lax263307Proofs.NativeMaximum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet

def advance (a : ℕ×ℕ) (q : ℚ) : ℕ×ℕ := maximumPair a.1 a.2 (clippedNumerator q) q.den

def maximum (qs : List ℚ) : ℕ×ℕ := qs.foldl advance (0,1)

theorem fold_bounds (M : ℕ) (a : ℕ×ℕ) (qs : List ℚ) (ha : a.1≤M ∧ a.2≤M ∧ 0<a.2)
    (hq : ∀ q∈qs,q.num.natAbs≤M ∧ q.den≤M) :
    (qs.foldl advance a).1≤M ∧ (qs.foldl advance a).2≤M ∧ 0<(qs.foldl advance a).2 := by
  induction qs generalizing a with
  | nil => exact ha
  | cons q qs ih =>
    apply ih
    · have hqn := (hq q (by simp)).1
      have hqd := (hq q (by simp)).2
      dsimp [advance,maximumPair]
      split_ifs
      · exact ⟨by unfold clippedNumerator; split_ifs <;> omega,hqd,q.den_pos⟩
      · exact ha
    · intro q hq'
      exact hq q (by simp [hq'])

theorem maximum_bounds (M : ℕ) (hM : 1≤M) (qs : List ℚ)
    (hq : ∀ q∈qs,q.num.natAbs≤M ∧ q.den≤M) :
    (maximum qs).1≤M ∧ (maximum qs).2≤M ∧ 0<(maximum qs).2 :=
  fold_bounds M (0,1) qs ⟨by omega,hM,by omega⟩ hq

theorem take_succ (qs : List ℚ) (i : ℕ) (hi : i<qs.length) :
    maximum (qs.take (i+1)) = advance (maximum (qs.take i)) qs[i] := by
  dsimp only [maximum]
  rw [List.take_succ_eq_append_getElem hi,List.foldl_append]
  rfl

def Invariant (front tail : List ℕ) (qs : List ℚ) (σ : Env) : Prop :=
  Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ ∧
  σ.vars "input.matrixLength"=front.length ∧ σ.vars "input.n"=qs.length ∧
  σ.vars "weight.i"≤qs.length ∧
  σ.vars "maximum.n"=(maximum (qs.take (σ.vars "weight.i"))).1 ∧
  σ.vars "maximum.d"=(maximum (qs.take (σ.vars "weight.i"))).2

theorem step_spec (B M : ℕ) (front tail : List ℕ) (qs : List ℚ) (hM : 1≤M)
    (hB : 2*M^2+3<B) (hlen : front.length+3*qs.length+3<B)
    (hwords : ∀ q∈qs,q.num.natAbs≤M ∧ q.den≤M) :
    Spec B (fun σ => Invariant front tail qs σ ∧ σ.vars "weight.i"<qs.length)
      maximumStep (fun σ τ => Invariant front tail qs τ ∧ τ.vars "weight.i"=σ.vars "weight.i"+1) 48 := by
  have hMB : M<B := by nlinarith only [hB]
  have hMM : M*M<B := by nlinarith only [hB]
  rintro σ ⟨⟨hp,hbase,hn,hi,hmaxn,hmaxd⟩,hlt⟩
  let i := σ.vars "weight.i"
  let a := maximum (qs.take i)
  have ha := maximum_bounds M hM (qs.take i) (fun q hq => hwords q (List.mem_of_mem_take hq))
  have hq := hwords qs[i] (List.getElem_mem hlt)
  have hc : clippedNumerator qs[i]≤M := by unfold clippedNumerator; split_ifs <;> omega
  have hl : a.1*qs[i].den<B := (Nat.mul_le_mul ha.1 hq.2).trans_lt hMM
  have hr : clippedNumerator qs[i]*a.2<B := (Nat.mul_le_mul hc ha.2.1).trans_lt hMM
  obtain ⟨τ,rr,hti,htn,htd⟩ := maximum_step_spec B a.1 a.2 front tail qs i hlt hlen
    (ha.1.trans_lt hMB) (ha.2.1.trans_lt hMB) (hq.1.trans_lt hMB) (hq.2.trans_lt hMB) hl hr
    σ ⟨hp,hbase,rfl,hmaxn,hmaxd⟩
  refine ⟨τ,rr,?_,hti⟩
  refine ⟨?_,?_,?_,by omega,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "input.data" (by decide)] using hp
  · exact (rr.frame_var "input.matrixLength" (by decide)).trans hbase
  · exact (rr.frame_var "input.n" (by decide)).trans hn
  · rw [hti,take_succ qs i hlt]
    exact htn
  · rw [hti,take_succ qs i hlt]
    exact htd

def command : Com := .seq (.assign "maximum.n" (.lit 0))
  (.seq (.assign "maximum.d" (.lit 1))
    (.seq (.assign "weight.i" (.lit 0))
      (.while (.lt (.var "weight.i") (.var "input.n")) maximumStep)))

theorem command_spec (B M : ℕ) (front tail : List ℕ) (qs : List ℚ) (hM : 1≤M)
    (hB : 2*M^2+3<B) (hlen : front.length+3*qs.length+3<B)
    (hwords : ∀ q∈qs,q.num.natAbs≤M ∧ q.den≤M) :
    Spec B (fun σ => Prefix (front++qs.flatMap encodeRational++tail) "input.data" σ ∧
      σ.vars "input.matrixLength"=front.length ∧ σ.vars "input.n"=qs.length)
      command (fun _ τ => τ.vars "maximum.n"=(maximum qs).1 ∧ τ.vars "maximum.d"=(maximum qs).2)
      (52*qs.length+10) := by
  have hlen' : qs.length<B := by omega
  have h1 : 1<B := by omega
  have hl := Spec.forRangeZero "weight.i" "input.n" (Invariant front tail qs) qs.length 48 hlen'
    (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) (step_spec B M front tail qs hM hB hlen hwords)
  rintro σ ⟨hp,hbase,hn⟩
  let ν := σ.setVar "maximum.n" 0
  let μ := ν.setVar "maximum.d" 1
  have r1 : Run B (.assign "maximum.n" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have r2 : Run B (.assign "maximum.d" (.lit 1)) ν μ 2 := Run.assign (evalB_lit h1)
  have hi : Invariant front tail qs (μ.setVar "weight.i" 0) := by
    refine ⟨hp,?_,?_,?_,?_,?_⟩
    · simpa only [μ,ν,vars_setVar,String.reduceEq,if_false] using hbase
    · simpa only [μ,ν,vars_setVar,String.reduceEq,if_false] using hn
    · simp only [vars_setVar,if_true]; omega
    · simp only [μ,ν,vars_setVar,String.reduceEq,if_false,if_true,List.take_zero,maximum,List.foldl_nil]
    · simp only [μ,ν,vars_setVar,String.reduceEq,if_false,if_true,List.take_zero,maximum,List.foldl_nil]
  obtain ⟨τ,rl,hpost⟩ := hl μ hi
  refine ⟨τ,(r1.seq (r2.seq rl)).mono (by omega),?_,?_⟩
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2.1
  · simpa only [hpost.2,List.take_length] using hpost.1.2.2.2.2.2


def value (a : ℕ×ℕ) : ℚ := (a.1:ℚ)/a.2

theorem advance_positive (a : ℕ×ℕ) (q : ℚ) (ha : 0<a.2) : 0<(advance a q).2 := by
  unfold advance maximumPair
  split_ifs
  · exact q.den_pos
  · exact ha

theorem advance_value (a : ℕ×ℕ) (q : ℚ) (ha : 0<a.2) :
    value (advance a q) = max (value a) (max q 0) := by
  dsimp only [advance,value]
  rw [maximum_pair_value _ _ _ _ ha q.den_pos,clipped_value]

theorem fold_le_iff (a : ℕ×ℕ) (ha : 0<a.2) (qs : List ℚ) (W : ℚ) :
    value (qs.foldl advance a)≤W ↔ value a≤W ∧ ∀ q∈qs,max q 0≤W := by
  induction qs generalizing a with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons,ih _ (advance_positive a q ha),advance_value a q ha]
    simp only [max_le_iff,List.mem_cons,forall_eq_or_imp]
    tauto

theorem maximum_value {n : ℕ} (w : Fin n → ℚ) :
    value (maximum (List.ofFn w)) =
      Lax263307.WeightRounding.maximumWeight (fun v => max (w v) 0) := by
  let W := Lax263307.WeightRounding.maximumWeight (fun v => max (w v) 0)
  have hzero : (0:ℚ)≤W := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hweight (v : Fin n) : max (w v) 0≤W := by
    apply Finset.le_max'
    simp
  have hupper : value (maximum (List.ofFn w))≤W := by
    apply (fold_le_iff (0,1) (by omega) (List.ofFn w) W).mpr
    refine ⟨by simpa [value] using hzero,?_⟩
    intro q hq
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq
    exact hweight v
  refine le_antisymm hupper ?_
  have hbound := (fold_le_iff (0,1) (by omega) (List.ofFn w) (value (maximum (List.ofFn w)))).mp le_rfl
  apply Finset.max'_le
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | hq
  · simpa [value] using hbound.1
  · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hq
    exact hbound.2 (w v) (List.mem_ofFn.mpr ⟨v,rfl⟩)

end Lax263307Proofs.NativeMaximum
