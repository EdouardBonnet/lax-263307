import Lax263307Proofs.NativeRestrictionRead
import Lax455465Proofs.RamFractionPrimitives

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeSplitEntry

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

def Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) (σ : Env) : Prop :=
  NativeRestrictionRead.Data G (fun v => (x v : ℚ)) R σ ∧ Stored "split.large" (large : ℚ) σ ∧
    σ.vars "split.order"=2*R.card ∧ σ.vars "split.count"=(2*R.card)*(2*R.card)

theorem frame {B n K : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → ℚ≥0} {R : Finset (Fin n)} {large : ℚ≥0} {c : Com} {σ τ : Env}
    (rr : Run B c σ τ K) (hd : Data G x R large σ)
    (ha : ∀ s∈["restrict.vertices","search.graph","near.costs"],s∉c.warrs)
    (hv : ∀ s∈["restrict.count","graph.n","split.large.s","split.large.n","split.large.d","split.order","split.count"],s∉c.wvars) :
    Data G x R large τ := by
  refine ⟨NativeRestrictionRead.frame rr hd.1 ha (by
      intro s hs
      apply hv s
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs ⊢
      tauto),?_,
    (rr.frame_var "split.order" (hv _ (by simp))).trans hd.2.2.1,
    (rr.frame_var "split.count" (hv _ (by simp))).trans hd.2.2.2⟩
  simpa only [Stored,String.reduceAppend,rr.frame_var "split.large.s" (hv _ (by simp)),
    rr.frame_var "split.large.n" (hv _ (by simp)),rr.frame_var "split.large.d" (hv _ (by simp))] using hd.2.1

def ports : Com := .seq (.assign "split.u" (.div (.var "split.i") (.var "split.order")))
  (.seq (.assign "split.v" (.sub (.var "split.i") (.mul (.var "split.u") (.var "split.order"))))
    (.seq (.assign "restrict.row" (.div (.var "split.u") (.lit 2)))
      (.seq (.assign "restrict.col" (.div (.var "split.v") (.lit 2)))
        (.seq (.assign "split.up" (.sub (.var "split.u") (.mul (.lit 2) (.var "restrict.row"))))
          (.assign "split.vp" (.sub (.var "split.v") (.mul (.lit 2) (.var "restrict.col"))))))))

theorem ports_spec (B s : ℕ) (i : Fin ((2*s)*(2*s))) (hB : (2*s)*(2*s)+2*s+4<B) :
    Spec B (fun σ => σ.vars "split.order"=2*s ∧ σ.vars "split.i"=i.val) ports
      (fun _ τ => τ.vars "split.u"=(NativeBlowUp.row i).val ∧
        τ.vars "split.v"=(NativeBlowUp.col i).val ∧
        τ.vars "restrict.row"=(original (NativeBlowUp.row i)).val ∧
        τ.vars "restrict.col"=(original (NativeBlowUp.col i)).val ∧
        τ.vars "split.up"=(NativeBlowUp.row i).val%2 ∧ τ.vars "split.vp"=(NativeBlowUp.col i).val%2) 30 := by
  have hn : 0<2*s := by have hh := i.isLt; nlinarith
  have hi := i.isLt
  have hdiv := Nat.div_le_self i.val (2*s)
  have hprod := Nat.div_mul_le_self i.val (2*s)
  have hmod := Nat.mod_lt i.val hn
  have hv : i.val-i.val/(2*s)*(2*s)=i.val%(2*s) := Nat.mod_eq_sub_div_mul.symm
  have hur : i.val / (2*s) / 2 * 2 ≤ i.val / (2*s) := Nat.div_mul_le_self _ _
  have hvr : (i.val%(2*s))/2*2 ≤ i.val%(2*s) := Nat.div_mul_le_self _ _
  have hup : i.val/(2*s)-2*(i.val/(2*s)/2)=i.val/(2*s)%2 := by
    rw [Nat.mul_comm 2 (i.val/(2*s)/2)]; exact Nat.mod_eq_sub_div_mul.symm
  have hvp : i.val%(2*s)-2*((i.val%(2*s))/2)=i.val%(2*s)%2 := by
    rw [Nat.mul_comm 2 ((i.val%(2*s))/2)]; exact Nat.mod_eq_sub_div_mul.symm
  run_vcg
  all_goals simp_all [NativeBlowUp.row,NativeBlowUp.col,original]
  all_goals omega

def choose : Com := .ite (.eq (.var "split.up") (.lit 0))
  (.ite (.eq (.var "split.v") (.add (.var "split.u") (.lit 1))) (load "split.cost") RamFractionPrimitives.zero)
  (.ite (.eq (.add (.var "split.v") (.lit 1)) (.var "split.u")) (load "split.large")
    (.ite (.eq (.var "split.vp") (.lit 0))
      (.ite (.eq (.var "restrict.edge") (.lit 1)) (load "split.large") RamFractionPrimitives.zero)
      RamFractionPrimitives.zero))

theorem choose_spec (B M s : ℕ) (G : SimpleGraph (Fin s)) [DecidableRel G.Adj]
    (x : Fin s → ℚ≥0) (large : ℚ≥0) (u v : Fin (2*s)) (hB : 2*s+M+4<B)
    (hx : Bounded M (x (original u) : ℚ)) (hl : Bounded M (large : ℚ)) :
    Spec B (fun σ => σ.vars "split.u"=u.val ∧ σ.vars "split.v"=v.val ∧
      σ.vars "split.up"=u.val%2 ∧ σ.vars "split.vp"=v.val%2 ∧
      σ.vars "restrict.edge"=(if G.Adj (original u) (original v) then 1 else 0) ∧
      Stored "split.cost" (x (original u) : ℚ) σ ∧ Stored "split.large" (large : ℚ) σ)
      choose (fun _ τ => RamRational.FractionOutput ((splitInstance G x large).capacity u v : ℚ) τ) 26 := by
  have hu := u.isLt
  have hv := v.isLt
  have hum := Nat.mod_lt u.val (by decide : 0<2)
  have hvm := Nat.mod_lt v.val (by decide : 0<2)
  have hcost := load_spec B "split.cost" (x (original u) : ℚ) (by omega)
    (hx.1.trans_lt (by omega)) (hx.2.trans_lt (by omega)) (by decide)
  have hlarge := load_spec B "split.large" (large : ℚ) (by omega)
    (hl.1.trans_lt (by omega)) (hl.2.trans_lt (by omega)) (by decide)
  have hzero := RamFractionPrimitives.zero_spec B (by omega)
  have hu01 : u.val%2=0 ∨ u.val%2=1 := by omega
  have hv01 : v.val%2=0 ∨ v.val%2=1 := by omega
  rcases hu01 with hu0 | hu1 <;> rcases hv01 with hv0 | hv1 <;>
    by_cases hadj : G.Adj (original u) (original v)
  all_goals run_vcg [hcost,hlarge,hzero]
  all_goals simp_all [splitInstance]
  all_goals omega

def command : Com := .seq ports (.seq NativeRestrictionRead.graphRead
  (.seq NativeRestrictionRead.costRead (.seq (save "split.cost") choose)))

theorem command_spec (B M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (R : Finset (Fin n)) (large : ℚ≥0) (i : Fin ((2*R.card)*(2*R.card)))
    (hB : 4*n*n+6*n+M+20<B) (hx : ∀ v,Bounded M (x v : ℚ)) (hl : Bounded M (large : ℚ)) :
    Spec B (fun σ => Data G x R large σ ∧ σ.vars "split.i"=i.val) command
      (fun _ τ => Data G x R large τ ∧ RamRational.FractionOutput
        ((splitInstance (restriction G R) (fun v => x (label R v)) large).capacity
          (NativeBlowUp.row i) (NativeBlowUp.col i) : ℚ) τ) 100 := by
  have hR := NativeMaskUnpack.card_bound R
  let u := NativeBlowUp.row i
  let v := NativeBlowUp.col i
  rintro σ ⟨hd,hi⟩
  obtain ⟨σ1,r1,p1⟩ := ports_spec B R.card i (by nlinarith only [hB,Nat.mul_le_mul hR hR,hR]) σ ⟨hd.2.2.1,hi⟩
  have d1 := frame r1 hd (by decide) (by decide)
  obtain ⟨σ2,r2,p2⟩ := NativeRestrictionRead.graph_spec B n G (fun v => (x v : ℚ)) R (original u) (original v)
    (by nlinarith only [hB]) σ1 ⟨d1.1,p1.2.2.1,p1.2.2.2.1⟩
  have hrow2 : σ2.vars "restrict.row"=(original u).val := (r2.frame_var "restrict.row" (by decide)).trans p1.2.2.1
  obtain ⟨σ3,r3,p3⟩ := NativeRestrictionRead.cost_spec B M n G (fun v => (x v : ℚ)) R (original u)
    (by omega) (by omega) hx σ2 ⟨p2.1,hrow2⟩
  have hcost := hx (label R (original u))
  obtain ⟨σ4,r4,p4⟩ := save_spec B "split.cost" (x (label R (original u)) : ℚ) (by omega)
    (hcost.1.trans_lt (by omega)) (hcost.2.trans_lt (by omega)) (by decide) σ3 p3.2
  have r1234 := r1.seq (r2.seq (r3.seq r4))
  have r234 := r2.seq (r3.seq r4)
  have d4 := frame r1234 hd (by decide) (by decide)
  obtain ⟨τ,r5,p5⟩ := choose_spec B M R.card (restriction G R) (fun v => x (label R v)) large u v
    (by omega) hcost hl σ4
    ⟨(r234.frame_var "split.u" (by decide)).trans p1.1,
      (r234.frame_var "split.v" (by decide)).trans p1.2.1,
      (r234.frame_var "split.up" (by decide)).trans p1.2.2.2.2.1,
      (r234.frame_var "split.vp" (by decide)).trans p1.2.2.2.2.2,
      ((r3.seq r4).frame_var "restrict.edge" (by decide)).trans p2.2,p4,d4.2.1⟩
  have rr := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  exact ⟨τ,rr.mono (by omega),frame rr hd (by decide) (by decide),p5⟩

theorem height (M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (hM : 1≤M) (hx : ∀ v,Bounded M (x v : ℚ))
    (hl : Bounded M (large : ℚ)) (u v : Fin (2*n)) :
    Bounded M ((splitInstance G x large).capacity u v : ℚ) := by
  dsimp [splitInstance]
  split_ifs <;> first | exact hx _ | exact hl | exact ⟨by simp,by simpa using hM⟩

end Lax263307Proofs.NativeSplitEntry
