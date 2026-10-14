import Lax263307Proofs.NativeMaskUnpack
import Lax263307.ComponentCutEncoding

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeComponentCoefficient

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks

def hits {n : ℕ} (A C J : Finset (Fin n)) : Finset (Fin n) :=
  C.filter fun v => insert v A = J

theorem hits_card {n : ℕ} (A C J : Finset (Fin n)) :
    ((hits A C J).card : ℤ) = ∑ v ∈ C, if insert v A = J then 1 else 0 := by
  simp only [hits,Finset.card_filter]
  push_cast
  rfl

def Context {n : ℕ} (A C J : Finset (Fin n)) (u : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "conditioning.choice"=mask A ∧
  σ.vars "component.mask"=mask C ∧ σ.vars "cut.column"=mask J ∧
  σ.vars "component.target"=u

theorem frame {n B K : ℕ} (A C J : Finset (Fin n)) (u : ℕ)
    {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    (h0 : "graph.n"∉c.wvars) (h1 : "conditioning.choice"∉c.wvars)
    (h2 : "component.mask"∉c.wvars) (h3 : "cut.column"∉c.wvars)
    (h4 : "component.target"∉c.wvars) (h : Context A C J u σ) : Context A C J u τ :=
  ⟨(rr.frame_var _ h0).trans h.1,(rr.frame_var _ h1).trans h.2.1,
    (rr.frame_var _ h2).trans h.2.2.1,(rr.frame_var _ h3).trans h.2.2.2.1,
    (rr.frame_var _ h4).trans h.2.2.2.2⟩

def selected : Cond := .eq
  (.and (.shiftr (.var "component.mask") (.var "cut.vertex")) (.lit 1)) (.lit 1)

def sameColumn : Cond := .eq
  (.or (.var "conditioning.choice") (.shiftl (.lit 1) (.var "cut.vertex"))) (.var "cut.column")

def increment : Com := .assign "coefficient.positive" (.add (.var "coefficient.positive") (.lit 1))

def collect : Com := .ite selected (.ite sameColumn increment .skip) .skip

def step : Com := .seq collect (.assign "cut.vertex" (.add (.var "cut.vertex") (.lit 1)))

def Invariant {n : ℕ} (A C J : Finset (Fin n)) (u : ℕ) (σ : Env) : Prop :=
  Context A C J u σ ∧ σ.vars "cut.vertex"≤n ∧
  σ.vars "coefficient.positive"=(initialSet (hits A C J) (σ.vars "cut.vertex")).card

private theorem value {B x : ℕ} {s : String} {σ : Env} (h : σ.vars s=x) (hx : x<B) :
    (Expr.var s).evalB B σ=some x := by
  rw [evalB_var_iff]
  exact ⟨h.symm,h ▸ hx⟩

theorem step_spec {n : ℕ} (B : ℕ) (A C J : Finset (Fin n)) (u : ℕ)
    (hB : n+u+10<B) (hm : 2^n<B) :
    Spec B (fun σ => Invariant A C J u σ ∧ σ.vars "cut.vertex"<n) step
      (fun σ τ => Invariant A C J u τ ∧ τ.vars "cut.vertex"=σ.vars "cut.vertex"+1) 24 := by
  rintro σ ⟨⟨hc,hle,hcount⟩,hlt⟩
  let i := σ.vars "cut.vertex"
  let v : Fin n := ⟨i,hlt⟩
  let count := (initialSet (hits A C J) i).card
  let bit : ℕ := if v∈C then 1 else 0
  have hiB : i<B := by omega
  have hbitB : bit<B := by dsimp [bit]; split_ifs <;> omega
  have hCB : mask C<B := (mask_bound C).trans hm
  have hAB : mask A<B := (mask_bound A).trans hm
  have hJB : mask J<B := (mask_bound J).trans hm
  have hIB : mask (insert v A)<B := (mask_bound _).trans hm
  have hpB : 2^i<B := (Nat.pow_le_pow_right (by decide) hle).trans_lt hm
  have hbit : (Expr.and (.shiftr (.var "component.mask") (.var "cut.vertex")) (.lit 1)).evalB B σ=some bit := by
    have hh := evalB_bin (op:=.and)
      (evalB_bin (op:=.shiftr) (value hc.2.2.1 hCB) (evalB_var hiB)
        ((Nat.div_le_self _ _).trans_lt hCB)) (evalB_lit (show 1<B by omega))
      (by change Nat.land (mask C/2^i) 1<B; rw [NativeMaskUnpack.bit_value C v]; exact hbitB)
    exact hh.trans (congrArg some (NativeMaskUnpack.bit_value C v))
  have hs : selected.evalB B σ=some (decide (v∈C)) := by
    have hh := evalB_condEq hbit (evalB_lit (show 1<B by omega))
    by_cases hv : v∈C <;> simpa [selected,Bool.beq_eq_decide_eq,bit,hv] using hh
  have hins : (Expr.or (.var "conditioning.choice") (.shiftl (.lit 1) (.var "cut.vertex"))).evalB B σ=some (mask (insert v A)) := by
    have hh := evalB_bin (op:=.or) (value hc.2.1 hAB)
      (evalB_bin (op:=.shiftl) (evalB_lit (show 1<B by omega)) (evalB_var hiB)
        (by change 1*2^i<B; simpa only [one_mul] using hpB))
      (by change Nat.lor (mask A) (1*2^i)<B; simpa only [one_mul,mask_insert] using hIB)
    simpa only [Bop.apply_or,Bop.apply_shiftl,one_mul,mask_insert] using hh
  have heq : sameColumn.evalB B σ=some (decide (insert v A=J)) := by
    have hh := evalB_condEq hins (value hc.2.2.2.1 hJB)
    have hinj : mask (insert v A)=mask J ↔ insert v A=J := (mask_injective n).eq_iff
    simpa only [sameColumn,Bool.beq_eq_decide_eq,hinj] using hh
  have hnext := NativeMaskUnpack.prefix_card_step (hits A C J) i hlt
  have hcountB : count+1<B := by
    have hh := NativeMaskUnpack.card_bound (initialSet (hits A C J) i)
    dsimp [count]
    omega
  obtain ⟨ν,rr,hpos⟩ : ∃ ν,Run B collect σ ν 20 ∧
      ν.vars "coefficient.positive"=(initialSet (hits A C J) (i+1)).card := by
    by_cases hv : v∈C
    · by_cases he : insert v A=J
      · let ν := σ.setVar "coefficient.positive" (count+1)
        have ri : Run B increment σ ν 4 := Run.assign (evalB_bin (op:=.add)
          (value hcount (by omega)) (evalB_lit (show 1<B by omega)) hcountB)
        have rr := Run.ite_true (d:=Com.skip) (by simpa only [he,decide_true] using heq) ri
        have rr' := Run.ite_true (d:=Com.skip) (by simpa only [hv,decide_true] using hs) rr
        refine ⟨ν,rr'.mono (by simp [selected,sameColumn,Cond.size,Expr.size]),?_⟩
        rw [hnext]
        simp [ν,count,hits,hv,he,v]
      · have rr := Run.ite_false (c:=increment) (by simpa only [he,decide_false] using heq) (Run.skip (σ:=σ))
        have rr' := Run.ite_true (d:=Com.skip) (by simpa only [hv,decide_true] using hs) rr
        refine ⟨σ,rr'.mono (by simp [selected,sameColumn,Cond.size,Expr.size]),?_⟩
        rw [hnext]
        change σ.vars "coefficient.positive"=count+(if v∈hits A C J then 1 else 0)
        simp only [hits,Finset.mem_filter,he,and_false,if_false,Nat.add_zero]
        exact hcount
    · have rr := Run.ite_false (c:=Com.ite sameColumn increment Com.skip)
        (by simpa only [hv,decide_false] using hs) (Run.skip (σ:=σ))
      refine ⟨σ,rr.mono (by simp [selected,Cond.size,Expr.size]),?_⟩
      rw [hnext]
      change σ.vars "coefficient.positive"=count+(if v∈hits A C J then 1 else 0)
      simp only [hits,Finset.mem_filter,hv,false_and,if_false,Nat.add_zero]
      exact hcount
  have hiν : ν.vars "cut.vertex"=i := rr.frame_var _ (by decide)
  let τ := ν.setVar "cut.vertex" (i+1)
  have r2 : Run B (.assign "cut.vertex" (.add (.var "cut.vertex") (.lit 1))) ν τ 4 :=
    Run.assign (evalB_bin (op:=.add) (value hiν hiB) (evalB_lit (show 1<B by omega))
      (by change i+1<B; omega))
  have total := rr.seq r2
  have ht : τ.vars "cut.vertex"=i+1 := by simp [τ]
  refine ⟨τ,total,⟨frame A C J u total (by decide) (by decide) (by decide) (by decide) (by decide) hc,
    by rw [ht]; omega,?_⟩,ht⟩
  rw [ht,r2.frame_var "coefficient.positive" (by decide)]
  exact hpos

def positive : Com := .seq (.assign "coefficient.positive" (.lit 0))
  (.seq (.assign "cut.vertex" (.lit 0)) (.while (.lt (.var "cut.vertex") (.var "graph.n")) step))

theorem positive_spec {n : ℕ} (B : ℕ) (A C J : Finset (Fin n)) (u : ℕ)
    (hB : n+u+10<B) (hm : 2^n<B) :
    Spec B (Context A C J u) positive
      (fun _ τ => Context A C J u τ ∧ τ.vars "coefficient.positive"=(hits A C J).card) (28*n+8) := by
  have hloop := Spec.forRangeZero "cut.vertex" "graph.n" (Invariant A C J u) n 24 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.1) (step_spec B A C J u hB hm)
  intro σ hc
  let ν := σ.setVar "coefficient.positive" 0
  have r1 : Run B (.assign "coefficient.positive" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (show 0<B by omega))
  have hi : Invariant A C J u (ν.setVar "cut.vertex" 0) := by
    refine ⟨?_,by simp,?_⟩
    · simpa [Context,ν,Env.setVar] using hc
    · simp [ν,prefix_zero]
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,
    by simpa only [p2.2,prefix_full] using p2.1.2.2⟩

def negative : Com := .ite (.eq (.var "conditioning.choice") (.var "cut.column"))
  (.assign "coefficient.negative" (.var "component.target")) (.assign "coefficient.negative" (.lit 0))

def command : Com := .seq positive negative

theorem command_spec {n r : ℕ} (B : ℕ) (A C : Finset (Fin n)) (J : Lax263307.LinearRelaxation.Coordinate n r)
    (u : ℕ) (hB : n+u+10<B) (hm : 2^n<B) :
    Spec B (Context A C J.val u) command
      (fun _ τ => Context A C J.val u τ ∧ τ.vars "coefficient.positive"<B ∧ τ.vars "coefficient.negative"<B ∧
        ((τ.vars "coefficient.positive" : ℕ) : ℚ)-τ.vars "coefficient.negative"=
          (Lax263307.ComponentCutEncoding.coefficient A C u J : ℚ)) (28*n+14) := by
  intro σ hc
  obtain ⟨ν,r1,p1⟩ := positive_spec B A C J.val u hB hm σ hc
  have hinj : mask A=mask J.val ↔ A=J.val := (mask_injective n).eq_iff
  have hn : Spec B (Context A C J.val u) negative
      (fun _ τ => τ.vars "coefficient.negative"=if A=J.val then u else 0) 6 := by
    intro ξ hd
    have haB : mask A<B := (mask_bound A).trans hm
    have hjB : mask J.val<B := (mask_bound J.val).trans hm
    have he : (Cond.eq (.var "conditioning.choice") (.var "cut.column")).evalB B ξ=
        some (decide (A=J.val)) := by
      have hh := evalB_condEq (value hd.2.1 haB) (value hd.2.2.2.1 hjB)
      simpa only [Bool.beq_eq_decide_eq,hinj] using hh
    by_cases heq : A=J.val
    · let τ := ξ.setVar "coefficient.negative" u
      have ri : Run B (.assign "coefficient.negative" (.var "component.target")) ξ τ 2 :=
        Run.assign (value hd.2.2.2.2 (by omega))
      refine ⟨τ,(Run.ite_true (d:=Com.assign "coefficient.negative" (.lit 0))
        (by simpa only [heq,decide_true] using he) ri).mono (by simp [Cond.size,Expr.size]),?_⟩
      simp [τ,heq]
    · let τ := ξ.setVar "coefficient.negative" 0
      have ri : Run B (.assign "coefficient.negative" (.lit 0)) ξ τ 2 :=
        Run.assign (evalB_lit (show 0<B by omega))
      refine ⟨τ,(Run.ite_false (c:=Com.assign "coefficient.negative" (.var "component.target"))
        (by simpa only [heq,decide_false] using he) ri).mono (by simp [Cond.size,Expr.size]),?_⟩
      simp [τ,heq]
  obtain ⟨τ,r2,p2⟩ := hn ν p1.1
  have hp : τ.vars "coefficient.positive"=(hits A C J.val).card :=
    (r2.frame_var _ (by decide)).trans p1.2
  refine ⟨τ,r1.seq r2,frame A C J.val u r2 (by decide) (by decide) (by decide) (by decide) (by decide) p1.1,
    by rw [hp]; exact (NativeMaskUnpack.card_bound _).trans_lt (by omega),
    by rw [p2]; split_ifs <;> omega,?_⟩
  rw [hp,p2,Lax263307.ComponentCutEncoding.coefficient,Int.cast_sub,←hits_card]
  split_ifs <;> simp

end Lax263307Proofs.NativeComponentCoefficient
