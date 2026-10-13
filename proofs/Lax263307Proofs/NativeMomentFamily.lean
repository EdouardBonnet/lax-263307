import Lax263307Proofs.NativeMomentProduce
import Lax263307Proofs.NativeMomentAssembly

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

/-! Native entry readers for the six fixed moment-matrix row families. -/

namespace Lax263307Proofs.NativeMomentFamily

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 MomentLP

inductive Kind
  | normalization | upper | nonindependent | monotone | massPositive | massNegative
  deriving DecidableEq

def rowCount (kind : Kind) (n r : ℕ) : ℕ := match kind with
  | .normalization => 2
  | .monotone => dimension n r*n
  | _ => dimension n r

def matrix (kind : Kind) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    Fin (rowCount kind n r) → Index n r → ℚ := match kind with
  | .normalization => NativeMomentAssembly.normalization n r
  | .upper => NativeMomentAssembly.upper n r
  | .nonindependent => NativeMomentAssembly.nonindependent G r
  | .monotone => NativeMomentAssembly.monotone n r
  | .massPositive => NativeMomentAssembly.massPositive n k r
  | .massNegative => NativeMomentAssembly.massNegative n k r

def entries (kind : Kind) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) : List ℚ :=
  (List.ofFn fun i => List.ofFn (matrix kind G k r i)).flatten

def coordinates : Com := .seq (.assign "family.row" (.div (.var "fill.i") (.var "catalog.count")))
  (.assign "column.index" (.sub (.var "fill.i") (.mul (.var "family.row") (.var "catalog.count"))))

def selectRow (kind : Kind) : Com := match kind with
  | .normalization => .assign "row.index" (.lit 0)
  | .monotone => .seq (.assign "row.index" (.div (.var "family.row") (.var "graph.n")))
      (.assign "row.v" (.sub (.var "family.row") (.mul (.var "row.index") (.var "graph.n"))))
  | _ => .assign "row.index" (.var "family.row")

def produce (kind : Kind) : Com := match kind with
  | .normalization => .ite (.eq (.var "family.row") (.lit 0)) NativeMomentProduce.singleCommand
      (.seq NativeMomentProduce.singleCommand NativeMomentProduce.swap)
  | .upper => NativeMomentProduce.singleCommand
  | .nonindependent => NativeMomentProduce.guard "row.independent" 0 NativeMomentProduce.singleCommand
  | .monotone => NativeMomentProduce.guard "row.active" 1 NativeMomentRows.monotoneCommand
  | .massPositive => NativeMomentProduce.guard "row.active" 1 NativeMomentRows.massCommand
  | .massNegative => .seq (NativeMomentProduce.guard "row.active" 1 NativeMomentRows.massCommand) NativeMomentProduce.swap

def read (kind : Kind) : Com := .seq coordinates (.seq (selectRow kind) (.seq NativeMomentAccess.command (produce kind)))

def appendMatrix (kind : Kind) : Com := NativeRationalTabulate.command (read kind)

theorem entries_words (kind : Kind) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    NativeRationalTabulate.words (entries kind G k r)=NativeMomentAssembly.matrixWords (matrix kind G k r) := rfl

theorem entries_length (kind : Kind) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    (entries kind G k r).length=rowCount kind n r*dimension n r := by
  simp [entries,List.length_flatten,List.map_ofFn,List.sum_ofFn]

theorem coordinates_spec (B q columns : ℕ) (hB : q+columns+3<B) :
    Spec B (fun σ => σ.vars "fill.i"=q ∧ σ.vars "catalog.count"=columns) coordinates
      (fun _ τ => τ.vars "family.row"=q/columns ∧ τ.vars "column.index"=q%columns) 10 := by
  have hdiv : q/columns≤q := Nat.div_le_self _ _
  have hmul : q/columns*columns≤q := Nat.div_mul_le_self _ _
  run_vcg
  all_goals simp_all [Env.setVar,Nat.mod_eq_sub_div_mul]
  all_goals omega

theorem candidates_first (n R : ℕ) : (RationalConditioning.candidates n R)[0]?=some (∅ : Finset (Fin n)) := by
  induction R with
  | zero => simp [RationalConditioning.candidates]
  | succ R ih =>
    rw [NativeCatalogOrder.all_candidates_succ]
    have hp : 0<(RationalConditioning.candidates n R).length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at ih
      contradiction
    rw [List.getElem?_append_left hp]
    exact ih

theorem dimension_positive (n r : ℕ) : 0<dimension n r := by
  have h := NativeCatalog.rows_positive n (r+2)
  change 1≤(NativeCatalog.rows n (r+3)).length at h
  rw [NativeCatalog.rows_words] at h
  simpa only [Lax263307.NativeCatalog.words,List.length_map,Nat.succ_le_iff] using h

theorem first_coordinate (n r : ℕ) :
    (CoordinateCatalog.indexing n r ⟨0,dimension_positive n r⟩).val=∅ := by
  have hi := NativeCatalogOrder.catalog_index n r ⟨0,dimension_positive n r⟩
  have he := candidates_first n (r+2)
  exact Option.some.inj (hi.symm.trans he)

def rowSlot (kind : Kind) (n r : ℕ) (i : Fin (rowCount kind n r)) : Index n r := match kind with
  | .normalization => ⟨0,dimension_positive n r⟩
  | .monotone => (finProdFinEquiv.symm i).1
  | .upper => i
  | .nonindependent => i
  | .massPositive => i
  | .massNegative => i

def Vertex (kind : Kind) (n r : ℕ) (i : Fin (rowCount kind n r)) (σ : Env) : Prop := match kind with
  | .monotone => σ.vars "row.v"=(finProdFinEquiv.symm i).2.val
  | _ => True

theorem select_row_spec (kind : Kind) (n r B : ℕ) (i : Fin (rowCount kind n r))
    (hB : i.val+n+3<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "family.row"=i.val) (selectRow kind)
      (fun _ τ => τ.vars "row.index"=(rowSlot kind n r i).val ∧ Vertex kind n r i τ) 10 := by
  have hdiv : i.val/n ≤ i.val := Nat.div_le_self _ _
  have hmul : i.val/n*n ≤ i.val := Nat.div_mul_le_self _ _
  cases kind <;> run_vcg
  all_goals simp_all [rowSlot,Vertex,Env.setVar,finProdFinEquiv,Fin.divNat,Fin.modNat,Nat.mod_eq_sub_div_mul]
  all_goals omega

def Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) (σ : Env) : Prop :=
  NativeMomentAccess.Data G r σ ∧ σ.vars "row.k"=k

def fixedVars : List String := ["graph.n","catalog.count","moment.r","row.k"]
def fixedArrays : List String := ["catalog.mask","search.graph","catalog.card","catalog.independent"]

theorem data_frame {n B K : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    (hv : ∀ x ∈ fixedVars,x∉c.wvars) (ha : ∀ x ∈ fixedArrays,x∉c.warrs)
    (hσ : Data G k r σ) : Data G k r τ := by
  refine ⟨⟨NativeCatalogMetadata.data_frame G r rr (hv _ (by decide)) (hv _ (by decide))
    (ha _ (by decide)) (ha _ (by decide)) hσ.1.1,?_,?_,?_⟩,?_⟩
  · simpa only [Lax455465Proofs.RamVirtualState.Prefix,rr.frame_arr "catalog.card" (ha _ (by decide))] using hσ.1.2.1
  · simpa only [Lax455465Proofs.RamVirtualState.Prefix,rr.frame_arr "catalog.independent" (ha _ (by decide))] using hσ.1.2.2.1
  · exact (rr.frame_var "moment.r" (hv _ (by decide))).trans hσ.1.2.2.2
  · exact (rr.frame_var "row.k" (hv _ (by decide))).trans hσ.2

open NativeCatalogMetadata NativeMomentProduce

def Ready (kind : Kind) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (i : Fin (rowCount kind n r)) (j : Index n r) (σ : Env) : Prop :=
  NativeMomentAccess.Loaded G r (rowSlot kind n r i) j σ ∧ σ.vars "graph.n"=n ∧
  σ.vars "row.k"=k ∧ σ.vars "row.active"=(if (atIndex n r (rowSlot kind n r i)).card ≤ r+1 then 1 else 0) ∧
  σ.vars "family.row"=i.val ∧ Vertex kind n r i σ

theorem produce_spec (kind : Kind) {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (i : Fin (rowCount kind n r)) (j : Index n r) (hB : n+k+3 < B) (hm : 2^n < B) :
    Spec B (Ready kind G k r i j) (produce kind)
      (fun _ τ => Value B (matrix kind G k r i j) τ) (22*n+50) := by
  rintro σ ⟨hl,hn,hk,ha,hi,hv⟩
  have h1 : 1 < B := by omega
  cases kind with
  | normalization =>
    change Fin 2 at i
    have hz : atIndex n r (rowSlot .normalization n r i)=∅ := first_coordinate n r
    obtain ⟨ν,r1,p1⟩ := single_spec B (atIndex n r (rowSlot .normalization n r i)) (atIndex n r j)
      h1 hm σ ⟨hl.1,hl.2.1⟩
    have pv : Value B (MomentLP.singleRow ∅ j) ν := by
      rw [hz] at p1
      simpa only [atIndex,NativeMomentRows.same_single_row] using p1
    have hiB : i.val < B := i.isLt.trans (by change 2 < B; omega)
    have hc : (Cond.eq (.var "family.row") (.lit 0)).evalB B σ=some (i.val==0) :=
      evalB_condEq (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩) (evalB_lit (show 0 < B by omega))
    by_cases he : i=0
    · have hei : i.val=0 := congrArg Fin.val he
      have rr := Run.ite_true (d := .seq singleCommand swap) (by simpa only [hei,beq_self_eq_true] using hc) r1
      exact ⟨ν,rr.mono (by simp [Cond.size,Expr.size]),by simpa only [matrix,NativeMomentAssembly.normalization,if_pos he] using pv⟩
    · have hei : i.val≠0 := fun hh => he (Fin.ext hh)
      obtain ⟨τ,r2,p2⟩ := swap_spec B (MomentLP.singleRow ∅ j) ν pv
      have rr := Run.ite_false (c := singleCommand) (by simpa only [beq_eq_false_iff_ne.mpr hei] using hc) (r1.seq r2)
      exact ⟨τ,rr.mono (by simp [Cond.size,Expr.size]),by simpa only [matrix,NativeMomentAssembly.normalization,if_neg he] using p2⟩
  | upper =>
    obtain ⟨τ,rr,p⟩ := single_spec B (atIndex n r i) (atIndex n r j) h1 hm σ ⟨hl.1,hl.2.1⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [atIndex,NativeMomentRows.same_single_row,matrix,NativeMomentAssembly.upper] using p
  | nonindependent =>
    have hf : σ.vars "row.independent"=(if ¬G.IsIndepSet (atIndex n r i : Set (Fin n)) then 0 else 1-0) := by
      by_cases h : G.IsIndepSet (atIndex n r i : Set (Fin n))
      · simpa [rowSlot,h] using hl.2.2.2
      · simpa [rowSlot,h] using hl.2.2.2
    obtain ⟨τ,rr,p⟩ := guard_spec B 0 8 "row.independent" _ (¬G.IsIndepSet (atIndex n r i : Set (Fin n)))
      (NativeMomentRows.same (atIndex n r i) (atIndex n r j)) singleCommand h1 (by omega)
      (single_spec B (atIndex n r i) (atIndex n r j) h1 hm) σ ⟨⟨hl.1,hl.2.1⟩,hf⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [atIndex,NativeMomentRows.same_single_row,ite_not,matrix,NativeMomentAssembly.nonindependent] using p
  | monotone =>
    let v : Fin n := (finProdFinEquiv.symm i).2
    let A := atIndex n r (finProdFinEquiv.symm i).1
    obtain ⟨τ,rr,p⟩ := guard_spec B 1 18 "row.active" _ (A.card ≤ r+1)
      ((NativeMomentRows.same (insert v A) (atIndex n r j) : ℚ)-NativeMomentRows.same A (atIndex n r j))
      NativeMomentRows.monotoneCommand h1 (by omega)
      (monotone_value_spec B A (atIndex n r j) v (by omega) hm) σ ⟨⟨hl.1,hl.2.1,hv⟩,ha⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [A,v,atIndex,NativeMomentRows.monotone_value,matrix,NativeMomentAssembly.monotone,ite_apply] using p
  | massPositive =>
    let A := atIndex n r i
    obtain ⟨τ,rr,p⟩ := guard_spec B 1 (22*n+18) "row.active" _ (A.card ≤ r+1)
      ((NativeMomentRows.matchCount A (atIndex n r j) n : ℚ)-(k*NativeMomentRows.same A (atIndex n r j) : ℕ))
      NativeMomentRows.massCommand h1 (by omega)
      (mass_value_spec B A (atIndex n r j) k (by omega) (by omega) hm) σ ⟨⟨hn,hl.1,hl.2.1,hk⟩,ha⟩
    refine ⟨τ,rr.mono (by omega),?_⟩
    simpa only [A,atIndex,NativeMomentRows.mass_value,matrix,NativeMomentAssembly.massPositive,ite_apply] using p
  | massNegative =>
    let A := atIndex n r i
    obtain ⟨ν,r1,p1⟩ := guard_spec B 1 (22*n+18) "row.active" _ (A.card ≤ r+1)
      ((NativeMomentRows.matchCount A (atIndex n r j) n : ℚ)-(k*NativeMomentRows.same A (atIndex n r j) : ℕ))
      NativeMomentRows.massCommand h1 (by omega)
      (mass_value_spec B A (atIndex n r j) k (by omega) (by omega) hm) σ ⟨⟨hn,hl.1,hl.2.1,hk⟩,ha⟩
    obtain ⟨τ,r2,p2⟩ := swap_spec B _ ν p1
    refine ⟨τ,(r1.seq r2).mono (by omega),?_⟩
    simpa only [A,atIndex,NativeMomentRows.mass_value,apply_ite,neg_zero,matrix,NativeMomentAssembly.massNegative] using p2

theorem entries_ofFn (kind : Kind) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    entries kind G k r=List.ofFn (fun z : Fin (rowCount kind n r*dimension n r) =>
      matrix kind G k r (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hh : (⟨i.val*dimension n r+j.val,by have h := j.isLt; have hi := i.isLt; nlinarith⟩ : Fin (rowCount kind n r*dimension n r))=finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  rw [hh,Equiv.symm_apply_apply]

theorem entries_get (kind : Kind) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (z : Fin (rowCount kind n r*dimension n r)) :
    (entries kind G k r)[z.val]?=some (matrix kind G k r (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) := by
  rw [entries_ofFn,List.getElem?_ofFn,dif_pos z.isLt]

theorem read_fixed_vars (kind : Kind) : ∀ x ∈ fixedVars,x∉(read kind).wvars := by
  cases kind <;> simp only [fixedVars,List.mem_cons,forall_eq_or_imp] <;> decide

theorem read_fixed_arrays (kind : Kind) : ∀ x ∈ fixedArrays,x∉(read kind).warrs := by
  cases kind <;> simp only [fixedArrays,List.mem_cons,forall_eq_or_imp] <;> decide

theorem read_spec (kind : Kind) {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (z : Fin (rowCount kind n r*dimension n r))
    (hB : rowCount kind n r*dimension n r+n+k+r+dimension n r+10 < B) (hm : 2^n < B) :
    Spec B (fun σ => Data G k r σ ∧ σ.vars "fill.i"=z.val) (read kind)
      (fun _ τ => Data G k r τ ∧ Value B
        (matrix kind G k r (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) τ) (22*n+90) := by
  rintro σ ⟨hd,hz⟩
  let i := (finProdFinEquiv.symm z).1
  let j := (finProdFinEquiv.symm z).2
  have hiq : i.val=z.val/dimension n r := rfl
  have hjq : j.val=z.val%dimension n r := rfl
  have hiq' : i.val ≤ z.val := by rw [hiq]; exact Nat.div_le_self _ _
  obtain ⟨ν,r1,p1⟩ := coordinates_spec B z.val (dimension n r) (by have h := z.isLt; omega) σ ⟨hz,hd.1.1.2.1⟩
  have d1 : Data G k r ν := data_frame G k r r1
    (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) hd
  obtain ⟨μ,r2,p2⟩ := select_row_spec kind n r B i (by have h := z.isLt; omega) ν ⟨d1.1.1.1,p1.1⟩
  have d2 : Data G k r μ := data_frame G k r r2
    (by cases kind <;> simp only [fixedVars,List.mem_cons,forall_eq_or_imp] <;> decide)
    (by cases kind <;> simp only [fixedArrays,List.mem_cons,forall_eq_or_imp] <;> decide) d1
  obtain ⟨ξ,r3,p3⟩ := NativeMomentAccess.command_spec B G r (rowSlot kind n r i) j (by omega) (by change dimension n r < B; omega) hm μ
    ⟨d2.1,p2.1,(r2.frame_var "column.index" (by cases kind <;> decide)).trans p1.2⟩
  have hn : ξ.vars "graph.n"=n := (r3.frame_var "graph.n" (by decide)).trans d2.1.1.1
  have hk : ξ.vars "row.k"=k := (r3.frame_var "row.k" (by decide)).trans d2.2
  have hir : ξ.vars "family.row"=i.val := ((r2.seq r3).frame_var "family.row" (by cases kind <;> decide)).trans p1.1
  have hv : Vertex kind n r i ξ := by
    cases kind <;> simp only [Vertex] at p2 ⊢
    all_goals first | trivial | exact (r3.frame_var "row.v" (by decide)).trans p2.2
  obtain ⟨τ,r4,p4⟩ := produce_spec kind B G k r i j (by omega) hm ξ ⟨p3.1,hn,hk,p3.2,hir,hv⟩
  have rr : Run B (read kind) σ τ (10+(10+(20+(22*n+50)))) := r1.seq (r2.seq (r3.seq r4))
  exact ⟨τ,rr.mono (by omega),data_frame G k r rr (read_fixed_vars kind) (read_fixed_arrays kind) hd,p4⟩

theorem append_matrix_spec (kind : Kind) {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (front : List ℕ)
    (hB : front.length+3*(rowCount kind n r*dimension n r)+n+k+r+dimension n r+10 < B) (hm : 2^n < B) :
    Spec B (fun σ => Data G k r σ ∧ σ.vars "fill.length"=rowCount kind n r*dimension n r ∧
      σ.vars "lp.length"=front.length ∧ front.length+3*(rowCount kind n r*dimension n r) ≤ (σ.arrs "lp.input").length ∧
      Lax455465Proofs.RamVirtualState.Prefix front "lp.input" σ)
      (appendMatrix kind) (fun _ τ => Data G k r τ ∧
        τ.vars "lp.length"=front.length+3*(rowCount kind n r*dimension n r) ∧
        Lax455465Proofs.RamVirtualState.Prefix (front++NativeMomentAssembly.matrixWords (matrix kind G k r)) "lp.input" τ)
      ((22*n+129)*(rowCount kind n r*dimension n r)+6) := by
  have hh := NativeRationalTabulate.command_spec B (entries kind G k r) front (Data G k r) (read kind) (22*n+90)
    (by rw [entries_length]; omega)
    (by cases kind <;> decide) (by cases kind <;> decide) (by cases kind <;> decide) (by cases kind <;> decide)
    (by intro σ h; simpa [Data,NativeMomentAccess.Data,NativeCatalogMetadata.Data,Lax455465Proofs.RamVirtualState.Prefix] using h)
    (by
      intro σ τ rr h
      exact data_frame G k r rr
        (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
        (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) h)
    (by
      intro σ τ rr h
      exact data_frame G k r rr
        (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
        (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) h)
    (by
      intro q hq σ hσ
      let z : Fin (rowCount kind n r*dimension n r) := ⟨q,by rwa [entries_length] at hq⟩
      obtain ⟨τ,rr,p⟩ := read_spec kind B G k r z (by omega) hm σ hσ
      have he := entries_get kind G k r z
      rw [List.getElem?_eq_getElem hq] at he
      exact ⟨τ,rr,p.1,by simpa only [Value,Option.some.inj he] using p.2⟩)
  simpa only [appendMatrix,entries_length,entries_words,show 22*n+90+39=22*n+129 by omega] using hh

def countExpr (kind : Kind) : Expr := match kind with
  | .normalization => .mul (.lit 2) (.var "catalog.count")
  | .monotone => .mul (.mul (.var "catalog.count") (.var "graph.n")) (.var "catalog.count")
  | _ => .mul (.var "catalog.count") (.var "catalog.count")

def command (kind : Kind) : Com := .seq (.assign "fill.length" (countExpr kind)) (appendMatrix kind)

theorem count_spec (kind : Kind) (n r B : ℕ)
    (hB : rowCount kind n r*dimension n r+n+dimension n r+3 < B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "catalog.count"=dimension n r)
      (.assign "fill.length" (countExpr kind))
      (fun _ τ => τ.vars "fill.length"=rowCount kind n r*dimension n r) 6 := by
  have hp := dimension_positive n r
  have hb : dimension n r*n ≤ dimension n r*n*dimension n r := Nat.le_mul_of_pos_right _ hp
  cases kind <;> simp only [rowCount,countExpr] at hB ⊢ <;> run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem command_spec (kind : Kind) {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (front : List ℕ)
    (hB : front.length+3*(rowCount kind n r*dimension n r)+n+k+r+dimension n r+10 < B) (hm : 2^n < B) :
    Spec B (fun σ => Data G k r σ ∧ σ.vars "lp.length"=front.length ∧
      front.length+3*(rowCount kind n r*dimension n r) ≤ (σ.arrs "lp.input").length ∧
      Lax455465Proofs.RamVirtualState.Prefix front "lp.input" σ)
      (command kind) (fun _ τ => Data G k r τ ∧
        τ.vars "lp.length"=front.length+3*(rowCount kind n r*dimension n r) ∧
        Lax455465Proofs.RamVirtualState.Prefix (front++NativeMomentAssembly.matrixWords (matrix kind G k r)) "lp.input" τ)
      ((22*n+129)*(rowCount kind n r*dimension n r)+12) := by
  rintro σ ⟨hd,hl,hr,hp⟩
  obtain ⟨ν,r1,p1⟩ := count_spec kind n r B (by omega) σ ⟨hd.1.1.1,hd.1.1.2.1⟩
  have d1 := data_frame G k r r1
    (by simp [fixedVars,Com.wvars])
    (by simp [fixedArrays,Com.warrs]) hd
  obtain ⟨τ,r2,p2⟩ := append_matrix_spec kind B G k r front hB hm ν
    ⟨d1,p1,(r1.frame_var "lp.length" (by simp [Com.wvars])).trans hl,
      by rwa [Lax455465Proofs.RamFrames.run_array_length r1],
      by simpa only [Lax455465Proofs.RamVirtualState.Prefix,r1.frame_arr "lp.input" (by simp [Com.warrs])] using hp⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),p2⟩

end Lax263307Proofs.NativeMomentFamily
