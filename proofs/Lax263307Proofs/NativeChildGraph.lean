import Lax263307Proofs.NativeRestrictionRead
import Lax263307Proofs.NativeMatrixOrder
import Lax263307Proofs.NativeTabulate

namespace Lax263307Proofs.NativeChildGraph

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeRestrictionRead

def read : Com := .seq (.assign "restrict.row" (.div (.var "fill.i") (.var "restrict.count")))
  (.seq (.assign "restrict.col" (.sub (.var "fill.i") (.mul (.var "restrict.row") (.var "restrict.count"))))
    (.seq graphRead (.assign "fill.value" (.var "restrict.edge"))))

theorem flat_entry {r : ℕ} (G : SimpleGraph (Fin r)) [DecidableRel G.Adj] (i : Fin (r*r)) :
    (NativeWeightReduction.adjacency G)[i.val]'(by rw [NativeWeightReduction.adjacency_length]; exact i.isLt)=
      if G.Adj (NativeBlowUp.row i) (NativeBlowUp.col i) then 1 else 0 := by
  have he := NativeMatrixOrder.flatten r (fun u v => if G.Adj u v then 1 else 0)
  change List.ofFn _ = NativeWeightReduction.adjacency G at he
  simp only [← he,List.getElem_ofFn]

theorem read_spec (B n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (i : ℕ)
    (hi : i<(NativeWeightReduction.adjacency (restriction G R)).length) (hB : n*n+n+3<B) :
    Spec B (fun σ => Data G x R σ ∧ σ.vars "fill.i"=i) read
      (fun _ τ => Data G x R τ ∧
        τ.vars "fill.value"=(NativeWeightReduction.adjacency (restriction G R))[i]) 25 := by
  have hir : i<R.card*R.card := by simpa only [NativeWeightReduction.adjacency_length] using hi
  let row := NativeBlowUp.row (⟨i,hir⟩ : Fin (R.card*R.card))
  let col := NativeBlowUp.col (⟨i,hir⟩ : Fin (R.card*R.card))
  have hr := NativeMaskUnpack.card_bound R
  have hiB : i<B := hir.trans_le (Nat.mul_self_le_mul_self hr) |>.trans (by omega)
  have hrow : row.val<B := row.isLt.trans_le hr |>.trans (by omega)
  have hcol : col.val<B := col.isLt.trans_le hr |>.trans (by omega)
  rintro σ ⟨hd,hs⟩
  let ν := σ.setVar "restrict.row" row.val
  have r1 : Run B (.assign "restrict.row" (.div (.var "fill.i") (.var "restrict.count"))) σ ν 4 :=
    Run.assign (evalB_bin (op:=.div)
      (by rw [evalB_var_iff]; exact ⟨hs.symm,hs ▸ hiB⟩)
      (by rw [evalB_var_iff]; exact ⟨hd.count.symm,hd.count ▸ (by omega : R.card<B)⟩)
      (by change i/R.card<B; exact hrow))
  have hd1 := frame r1 hd (by decide) (by decide)
  let μ := ν.setVar "restrict.col" col.val
  have hmul : row.val*R.card ≤ i := Nat.div_mul_le_self i R.card
  have r2 : Run B (.assign "restrict.col" (.sub (.var "fill.i") (.mul (.var "restrict.row") (.var "restrict.count")))) ν μ 6 := by
    apply Run.assign
    change (Expr.sub (.var "fill.i") (.mul (.var "restrict.row") (.var "restrict.count"))).evalB B ν=some (i%R.card)
    rw [Nat.mod_eq_sub_div_mul]
    exact evalB_bin (op:=.sub)
      (by rw [evalB_var_iff]; exact ⟨((r1.frame_var "fill.i" (by decide)).trans hs).symm,
        ((r1.frame_var "fill.i" (by decide)).trans hs) ▸ hiB⟩)
      (evalB_bin (op:=.mul) (by rw [evalB_var_iff]; simp only [ν,vars_setVar,if_true]; exact ⟨rfl,hrow⟩)
        (by rw [evalB_var_iff]; exact ⟨hd1.count.symm,hd1.count ▸ (by omega : R.card<B)⟩)
        (by change row.val*R.card<B; omega))
      (by change i-row.val*R.card<B; omega)
  have hd2 := frame r2 hd1 (by decide) (by decide)
  obtain ⟨ρ,r3,p3⟩ := graph_spec B n G x R row col hB μ
    ⟨hd2,(r2.frame_var "restrict.row" (by decide)).trans (by simp [ν]),by simp [μ]⟩
  let bit : ℕ := if (restriction G R).Adj row col then 1 else 0
  have hb : bit<B := by dsimp [bit]; split_ifs <;> omega
  let τ := ρ.setVar "fill.value" bit
  have r4 : Run B (.assign "fill.value" (.var "restrict.edge")) ρ τ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨p3.2.symm,p3.2 ▸ hb⟩)
  exact ⟨τ,r1.seq (r2.seq (r3.seq r4)),frame r4 p3.1 (by decide) (by decide),
    by simpa only [τ,vars_setVar,if_true] using (flat_entry (restriction G R) ⟨i,hir⟩).symm⟩

def command : Com := .seq (.assign "fill.length" (.mul (.var "restrict.count") (.var "restrict.count")))
  (NativeTabulate.command "child.graph" read)

/-- Construct the actual induced child graph in its canonical vertex
order, leaving the parent graph and the labeling table available. -/
theorem command_spec (B n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (R : Finset (Fin n)) (hB : n*n+n+3<B) :
    Spec B (fun σ => Data G x R σ ∧ R.card*R.card≤(σ.arrs "child.graph").length) command
      (fun _ τ => Data G x R τ ∧ Prefix (NativeWeightReduction.adjacency (restriction G R)) "child.graph" τ)
      (36*(R.card*R.card)+10) := by
  let xs := NativeWeightReduction.adjacency (restriction G R)
  have hlen : xs.length=R.card*R.card := NativeWeightReduction.adjacency_length _
  have hr := NativeMaskUnpack.card_bound R
  have hsq := Nat.mul_self_le_mul_self hr
  have hv := NativeTabulate.command_spec B xs "child.graph" (Data G x R) read 25
    (by rw [hlen]; omega)
    (by
      intro z hz
      have hbit : z=0 ∨ z=1 := by
        obtain ⟨row,hrow,hz⟩ := List.mem_flatten.mp hz
        obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hrow
        obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hz
        split_ifs <;> simp
      rcases hbit with rfl | rfl <;> omega)
    (by decide) (by decide) (by decide)
    (by
      intro σ hd
      have rr : Run B (.assign "fill.i" (.lit 0)) σ (σ.setVar "fill.i" 0) 2 := Run.assign (evalB_lit (by omega))
      exact frame rr hd (by decide) (by decide))
    (fun _ _ rr hd => frame rr hd (by decide) (by decide))
    (fun i hi => read_spec B n G x R i hi hB)
  rintro σ ⟨hd,hroom⟩
  let ν := σ.setVar "fill.length" (R.card*R.card)
  have r1 : Run B (.assign "fill.length" (.mul (.var "restrict.count") (.var "restrict.count"))) σ ν 4 :=
    Run.assign (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hd.count.symm,hd.count ▸ (by omega : R.card<B)⟩)
      (by rw [evalB_var_iff]; exact ⟨hd.count.symm,hd.count ▸ (by omega : R.card<B)⟩)
      (by change R.card*R.card<B; omega))
  obtain ⟨τ,r2,p2⟩ := hv ν ⟨frame r1 hd (by decide) (by decide),by simp [ν,hlen],by simpa only [ν,arrs_setVar,hlen] using hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hlen]; omega),p2⟩

end Lax263307Proofs.NativeChildGraph
