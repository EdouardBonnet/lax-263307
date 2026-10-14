import Lax263307Proofs.NativeQuadraticProduct

namespace Lax263307Proofs.NativeQuadraticTerms

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic

def term {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n → ℚ) (i : Fin (n*n)) : ℚ :=
  if G.Adj (NativeBlowUp.row i) (NativeBlowUp.col i) then
    a (NativeBlowUp.row i)*a (NativeBlowUp.col i) else 0

def terms {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n → ℚ) : List ℚ :=
  List.ofFn (term G a)

theorem terms_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n → ℚ) :
    (terms G a).sum=∑ u,∑ v,if G.Adj u v then a u*a v else 0 := by
  unfold terms
  rw [List.ofFn_mul,List.sum_flatten,List.map_ofFn,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro u _
  dsimp only [Function.comp_def]
  rw [List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro v _
  have hn : 0<n := by have hu := u.isLt; omega
  have hrow : NativeBlowUp.row ⟨u.val*n+v.val,by nlinarith [u.isLt,v.isLt]⟩=u := by
    apply Fin.ext
    change (u.val*n+v.val)/n=u.val
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt v.isLt,Nat.zero_add]
  have hcol : NativeBlowUp.col ⟨u.val*n+v.val,by nlinarith [u.isLt,v.isLt]⟩=v := by
    apply Fin.ext
    simp [NativeBlowUp.col,Nat.mod_eq_of_lt v.isLt]
  simp only [term,hrow,hcol]

def Context {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n → ℚ) (σ : Env) : Prop :=
  NativeCutRead.Context a σ ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ

def readEdge : Com := .assign "quadratic.edge" (.get "search.graph" (.var "quadratic.i"))

def finish : Com := .ite (.eq (.var "quadratic.edge") (.lit 0))
  RamFractionPrimitives.zero NativeQuadraticProduct.command

def command : Com := .seq readEdge finish

theorem command_spec (B M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n → ℚ) (i : Fin (n*n)) (hB : 2*M^2+3<B) (hs : n*n+3*n+10<B)
    (ha : ∀ j,Bounded M (a j)) :
    Spec B (fun σ => Context G a σ ∧ σ.vars "quadratic.i"=i.val) command
      (fun _ τ => Context G a τ ∧ FractionOutput (term G a i) τ) (36*(M^2).size+137) := by
  rintro σ ⟨hc,hi⟩
  have h1 : 1<B := by nlinarith
  let edge : ℕ := if G.Adj (NativeBlowUp.row i) (NativeBlowUp.col i) then 1 else 0
  have heB : edge<B := by dsimp [edge]; split_ifs <;> omega
  have hw : (NativeWeightReduction.adjacency G)[i.val]?=some edge :=
    NativeBlowUp.matrix_flat_coordinate (fun u v => if G.Adj u v then 1 else 0) i
  have hlen : i.val<(NativeWeightReduction.adjacency G).length := by
    rw [NativeWeightReduction.adjacency_length]; exact i.isLt
  rw [List.getElem?_eq_getElem hlen] at hw
  have hg := (hc.2 i.val hlen).trans hw
  let ν := σ.setVar "quadratic.edge" edge
  have r1 : Run B readEdge σ ν 3 := Run.assign
    (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ (by have hh := i.isLt; omega : i.val<B)⟩) hg heB)
  have hcν : NativeCutRead.Context a ν := by
    simpa only [NativeCutRead.Context,Prefix,r1.frame_arr "cut.source" (by decide),
      r1.frame_var "projection.n" (by decide)] using hc.1
  have hiν : ν.vars "quadratic.i"=i.val := (r1.frame_var "quadratic.i" (by decide)).trans hi
  by_cases he : G.Adj (NativeBlowUp.row i) (NativeBlowUp.col i)
  · obtain ⟨τ,r2,p2⟩ := NativeQuadraticProduct.command_spec B M n a i hB hs ha ν ⟨hcν,hiν⟩
    have hcond : (Cond.eq (.var "quadratic.edge") (.lit 0)).evalB B ν=some false := by
      have hval : ν.vars "quadratic.edge"=1 := by simp [ν,edge,he]
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hval.symm,hval ▸ h1⟩) (evalB_lit (by omega : 0<B))]
      rfl
    have rr := r1.seq (Run.ite_false (c := RamFractionPrimitives.zero) hcond r2)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),⟨p2.1,?_⟩,?_⟩
    · simpa only [Prefix,rr.frame_arr "search.graph" (by decide)] using hc.2
    · simpa only [term,if_pos he] using p2.2
  · obtain ⟨τ,r2,p2⟩ := RamFractionPrimitives.zero_spec B h1 ν trivial
    have hcond : (Cond.eq (.var "quadratic.edge") (.lit 0)).evalB B ν=some true := by
      have hval : ν.vars "quadratic.edge"=0 := by simp [ν,edge,he]
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hval.symm,hval ▸ (by omega : 0<B)⟩) (evalB_lit (by omega : 0<B))]
      rfl
    have rr := r1.seq (Run.ite_true (d := NativeQuadraticProduct.command) hcond r2)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_,?_⟩
    · simpa only [Context,NativeCutRead.Context,Prefix,rr.frame_arr "cut.source" (by decide),
        rr.frame_arr "search.graph" (by decide),rr.frame_var "projection.n" (by decide)] using hc
    · simpa only [term,if_neg he] using p2

end Lax263307Proofs.NativeQuadraticTerms
