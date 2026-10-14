import Lax263307Proofs.NativeRestrictionOrder
import Lax263307Proofs.NativeRationalRead
import Lax263307Proofs.NativeBlowUp
import Lax263307Proofs.NativeSignedArithmetic

set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeRestrictionRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeSignedArithmetic

structure Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (σ : Env) : Prop where
  labels : Prefix (NativeRestrictionOrder.words R) "restrict.vertices" σ
  graph : Prefix (NativeWeightReduction.adjacency G) "search.graph" σ
  costs : Prefix (encodeVector x) "near.costs" σ
  count : σ.vars "restrict.count"=R.card
  order : σ.vars "graph.n"=n

theorem frame {B n K : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → ℚ} {R : Finset (Fin n)} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    (hd : Data G x R σ)
    (ha : ∀ s∈["restrict.vertices","search.graph","near.costs"],s∉c.warrs)
    (hv : ∀ s∈["restrict.count","graph.n"],s∉c.wvars) : Data G x R τ := by
  refine ⟨?_,?_,?_,(rr.frame_var "restrict.count" (hv _ (by simp))).trans hd.count,
    (rr.frame_var "graph.n" (hv _ (by simp))).trans hd.order⟩
  · simpa only [Prefix,rr.frame_arr "restrict.vertices" (ha _ (by simp))] using hd.labels
  · simpa only [Prefix,rr.frame_arr "search.graph" (ha _ (by simp))] using hd.graph
  · simpa only [Prefix,rr.frame_arr "near.costs" (ha _ (by simp))] using hd.costs

theorem label_get {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → ℚ} {R : Finset (Fin n)} {σ : Env} (hd : Data G x R σ) (i : Fin R.card) :
    (σ.arrs "restrict.vertices")[i.val]?=some (ComputedSeparators.label R i).val := by
  simpa only [NativeRestrictionOrder.words,List.getElem_ofFn] using
    hd.labels i.val (by simpa only [NativeRestrictionOrder.words,List.length_ofFn] using i.isLt)

def graphRead : Com := .seq (.assign "restrict.u" (.get "restrict.vertices" (.var "restrict.row")))
  (.seq (.assign "restrict.v" (.get "restrict.vertices" (.var "restrict.col")))
    (.assign "restrict.edge" (.get "search.graph" (.add (.mul (.var "restrict.u") (.var "graph.n")) (.var "restrict.v")))))

theorem graph_spec (B n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (i j : Fin R.card) (hB : n*n+n+3<B) :
    Spec B (fun σ => Data G x R σ ∧ σ.vars "restrict.row"=i.val ∧ σ.vars "restrict.col"=j.val)
      graphRead (fun _ τ => Data G x R τ ∧
        τ.vars "restrict.edge"=if (ComputedSeparators.restriction G R).Adj i j then 1 else 0) 13 := by
  let u := ComputedSeparators.label R i
  let v := ComputedSeparators.label R j
  have hiB : i.val<B := i.isLt.trans_le (NativeMaskUnpack.card_bound R) |>.trans (by omega)
  have hjB : j.val<B := j.isLt.trans_le (NativeMaskUnpack.card_bound R) |>.trans (by omega)
  have huB : u.val<B := u.isLt.trans (by omega)
  have hvB : v.val<B := v.isLt.trans (by omega)
  have hind : u.val*n+v.val<n*n := by nlinarith [u.isLt,v.isLt]
  rintro σ ⟨hd,hi,hj⟩
  let ν := σ.setVar "restrict.u" u.val
  have r1 : Run B (.assign "restrict.u" (.get "restrict.vertices" (.var "restrict.row"))) σ ν 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (label_get hd i) huB)
  let μ := ν.setVar "restrict.v" v.val
  have r2 : Run B (.assign "restrict.v" (.get "restrict.vertices" (.var "restrict.col"))) ν μ 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; simpa only [ν,vars_setVar,String.reduceEq,if_false] using
      (show j.val=σ.vars "restrict.col" ∧ σ.vars "restrict.col"<B from ⟨hj.symm,hj ▸ hjB⟩)) (label_get hd j) hvB)
  have hget := NativeBlowUp.matrix_coordinate (fun a b => if G.Adj a b then 1 else 0) u v
  change (NativeWeightReduction.adjacency G)[u.val*n+v.val]?=some (if G.Adj u v then 1 else 0) at hget
  have hlen : u.val*n+v.val<(NativeWeightReduction.adjacency G).length := by
    rw [NativeWeightReduction.adjacency_length]; exact hind
  rw [List.getElem?_eq_getElem hlen] at hget
  have hg := (hd.graph _ hlen).trans hget
  let bit : ℕ := if G.Adj u v then 1 else 0
  let τ := μ.setVar "restrict.edge" bit
  have hgμ : (μ.arrs "search.graph")[u.val*n+v.val]?=some bit := hg
  have r3 : Run B (.assign "restrict.edge" (.get "search.graph" (.add (.mul (.var "restrict.u") (.var "graph.n")) (.var "restrict.v")))) μ τ 7 := by
    apply Run.assign
    apply evalB_get _ hgμ (by dsimp [bit]; split_ifs <;> omega)
    apply evalB_bin (op:=.add) _ _ (hind.trans (by omega))
    · apply evalB_bin (op:=.mul)
        (by rw [evalB_var_iff]; simp [μ,ν,huB])
        (by rw [evalB_var_iff]; simp only [μ,ν,vars_setVar,String.reduceEq,if_false]; exact ⟨hd.order.symm,hd.order ▸ (by omega : n<B)⟩)
        (by change u.val*n<B; nlinarith only [hind,hB])
    · rw [evalB_var_iff]
      simp [μ,hvB]
  have rr := r1.seq (r2.seq r3)
  exact ⟨τ,rr,frame rr hd (by decide) (by decide),by simp [τ,bit,u,v,ComputedSeparators.restriction]⟩

def costRead : Com := .seq (.assign "restrict.u" (.get "restrict.vertices" (.var "restrict.row")))
  (.seq (.assign "read.cursor" (.mul (.lit 3) (.var "restrict.u"))) (NativeRationalRead.command "near.costs"))

theorem cost_spec (B M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (i : Fin R.card) (hB : 3*n+10<B) (hM : M<B)
    (hx : ∀ v,Bounded M (x v)) :
    Spec B (fun σ => Data G x R σ ∧ σ.vars "restrict.row"=i.val) costRead
      (fun _ τ => Data G x R τ ∧ RamRational.FractionOutput (x (ComputedSeparators.label R i)) τ) 24 := by
  let u := ComputedSeparators.label R i
  have hiB : i.val<B := i.isLt.trans_le (NativeMaskUnpack.card_bound R) |>.trans (by omega)
  have huB : u.val<B := u.isLt.trans (by omega)
  rintro σ ⟨hd,hi⟩
  let ν := σ.setVar "restrict.u" u.val
  have r1 : Run B (.assign "restrict.u" (.get "restrict.vertices" (.var "restrict.row"))) σ ν 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (label_get hd i) huB)
  let μ := ν.setVar "read.cursor" (3*u.val)
  have r2 : Run B (.assign "read.cursor" (.mul (.lit 3) (.var "restrict.u"))) ν μ 4 :=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; simp [ν,huB]) (by change 3*u.val<B; have hh := u.isLt; omega))
  obtain ⟨τ,r3,p3⟩ := NativeRationalRead.vector_entry_spec B "near.costs" [] [] (List.ofFn x) u.val
    (by simpa only [List.length_ofFn] using u.isLt) (by omega) (by have hh := u.isLt; simp; omega)
    (by simpa only [List.getElem_ofFn] using (hx u).1.trans_lt hM)
    (by simpa only [List.getElem_ofFn] using (hx u).2.trans_lt hM) μ
    ⟨by simpa only [NativeRationalTabulate.words,encodeVector,List.nil_append,List.append_nil,Prefix,
        (r1.seq r2).frame_arr "near.costs" (by decide)] using hd.costs,by simp [μ]⟩
  have rr := r1.seq (r2.seq r3)
  exact ⟨τ,rr,frame rr hd (by decide) (by decide),by simpa only [List.getElem_ofFn] using p3.1⟩

end Lax263307Proofs.NativeRestrictionRead
