import Lax263307Proofs.NativeZeroScan

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeIndependentTest

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

def pairValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) (u v : Fin n) : ℕ :=
  (if u∈I then 1 else 0)*(if v∈I then 1 else 0)*(if G.Adj u v then 1 else 0)

theorem pair_value_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) (u v : Fin n) : pairValue G I u v≤1 := by
  unfold pairValue
  split_ifs <;> norm_num

theorem pair_value_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) (u v : Fin n) : pairValue G I u v=0 ↔ (u∈I → v∈I → ¬G.Adj u v) := by
  unfold pairValue
  split_ifs <;> simp_all

def values {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) : List ℕ :=
  List.ofFn fun q : Fin (n*n) => pairValue G I (NativeBlowUp.row q) (NativeBlowUp.col q)

theorem values_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) : (values G I).length=n*n := List.length_ofFn

theorem values_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) :
    NativeZeroScan.prefixOK (values G I) (n*n)=1 ↔ G.IsIndepSet (I : Set (Fin n)) := by
  rw [←values_length G I,NativeZeroScan.prefix_ok_full]
  constructor
  · intro h u hu v hv huv
    let q : Fin (n*n) := ⟨u.val*n+v.val,by nlinarith only [u.isLt,v.isLt]⟩
    have hn : 0<n := by omega
    have hrow : NativeBlowUp.row q=u := by
      apply Fin.ext
      dsimp [NativeBlowUp.row,q]
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hn,Nat.div_eq_of_lt v.isLt]
      omega
    have hcol : NativeBlowUp.col q=v := by
      apply Fin.ext
      simp [NativeBlowUp.col,q,Nat.add_mod,Nat.mod_eq_of_lt v.isLt]
    have hh := h _ (List.mem_ofFn.mpr ⟨q,rfl⟩)
    rw [hrow,hcol,pair_value_zero] at hh
    exact hh hu hv
  · intro h z hz
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hz
    rw [pair_value_zero]
    intro hu hv hadj
    exact h hu hv hadj.ne hadj

def read (graphArray membershipArray : String) : Com :=
  .seq (.assign "test.row" (.div (.var "test.i") (.var "graph.n")))
  (.seq (.assign "test.col" (.sub (.var "test.i") (.mul (.var "test.row") (.var "graph.n"))))
    (.assign "test.bit" (.mul
      (.mul (.get membershipArray (.var "test.row")) (.get membershipArray (.var "test.col")))
      (.get graphArray (.var "test.i")))))

theorem read_spec (B n q a b e : ℕ) (graphArray membershipArray : String)
    (hB : n*n+n+3<B) (hq : q<n*n) (ha : a≤1) (hb : b≤1) (he : e≤1) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "test.i"=q ∧
      (σ.arrs membershipArray)[q/n]?=some a ∧ (σ.arrs membershipArray)[q%n]?=some b ∧
      (σ.arrs graphArray)[q]?=some e) (read graphArray membershipArray)
      (fun _ τ => τ.vars "test.bit"=a*b*e) 24 := by
  have hn : 0<n := by nlinarith only [hq]
  have hqn : q/n<n := (Nat.div_lt_iff_lt_mul hn).mpr hq
  have hmod : q%n<n := Nat.mod_lt _ hn
  have hqB : q<B := by omega
  have hdivmul : q/n*n≤q := Nat.div_mul_le_self _ _
  have hab : a*b≤1 := by nlinarith only [Nat.mul_le_mul ha hb]
  have habe : a*b*e≤1 := by nlinarith only [Nat.mul_le_mul hab he]
  rintro σ ⟨hnσ,hqσ,haσ,hbσ,heσ⟩
  have hrooma : q/n<(σ.arrs membershipArray).length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at haσ
    contradiction
  have hroomb : q%n<(σ.arrs membershipArray).length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at hbσ
    contradiction
  have hroome : q<(σ.arrs graphArray).length := by
    by_contra hh
    rw [List.getElem?_eq_none (by omega)] at heσ
    contradiction
  run_vcg
  all_goals simp_all [Env.setVar,←Nat.mod_eq_sub_div_mul]
  all_goals omega

def Representation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) (graphArray membershipArray : String) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ Prefix (NativeWeightReduction.adjacency G) graphArray σ ∧
    Prefix (encodeOutput I) membershipArray σ

theorem read_graph_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) (graphArray membershipArray : String) (hB : n*n+n+3<B)
    (q : ℕ) (hq : q<(values G I).length) :
    Spec B (fun σ => Representation G I graphArray membershipArray σ ∧ σ.vars "test.i"=q)
      (read graphArray membershipArray)
      (fun _ τ => Representation G I graphArray membershipArray τ ∧ τ.vars "test.bit"=(values G I)[q]) 24 := by
  have hq' : q<n*n := by rwa [values_length] at hq
  let u := NativeBlowUp.row (⟨q,hq'⟩ : Fin (n*n))
  let v := NativeBlowUp.col (⟨q,hq'⟩ : Fin (n*n))
  let a := if u∈I then 1 else 0
  let b := if v∈I then 1 else 0
  let e := if G.Adj u v then 1 else 0
  have ha : a≤1 := by dsimp [a]; split_ifs <;> omega
  have hb : b≤1 := by dsimp [b]; split_ifs <;> omega
  have he : e≤1 := by dsimp [e]; split_ifs <;> omega
  rintro σ ⟨⟨hn,hgraph,hmem⟩,hqi⟩
  have hua : (σ.arrs membershipArray)[q/n]?=some a := by
    have hh := hmem u.val (by simp [encodeOutput])
    simpa [encodeOutput,a,u,NativeBlowUp.row] using hh
  have hvb : (σ.arrs membershipArray)[q%n]?=some b := by
    have hh := hmem v.val (by simp [encodeOutput])
    simpa [encodeOutput,b,v,NativeBlowUp.col] using hh
  have hge : (σ.arrs graphArray)[q]?=some e := by
    have hh := hgraph q (by rwa [NativeWeightReduction.adjacency_length])
    have hc := NativeBlowUp.matrix_flat_coordinate (fun u v => if G.Adj u v then 1 else 0) (⟨q,hq'⟩ : Fin (n*n))
    change (NativeWeightReduction.adjacency G)[q]?=some e at hc
    rw [List.getElem?_eq_getElem (by rwa [NativeWeightReduction.adjacency_length])] at hc
    exact hh.trans hc
  obtain ⟨τ,rr,p⟩ := read_spec B n q a b e graphArray membershipArray hB hq' ha hb he σ
    ⟨hn,hqi,hua,hvb,hge⟩
  refine ⟨τ,rr,⟨(rr.frame_var "graph.n" (by simp [read,Com.wvars])).trans hn,?_,?_⟩,?_⟩
  · simpa only [Prefix,rr.frame_arr graphArray (by simp [read,Com.warrs])] using hgraph
  · simpa only [Prefix,rr.frame_arr membershipArray (by simp [read,Com.warrs])] using hmem
  · simpa [values,pairValue,a,b,e,u,v] using p

def command (graphArray membershipArray : String) : Com := .seq
  (.assign "test.limit" (.mul (.var "graph.n") (.var "graph.n")))
  (NativeZeroScan.command (read graphArray membershipArray))

theorem command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (I : Finset (Fin n)) (graphArray membershipArray : String) (hB : n*n+n+3<B) :
    Spec B (Representation G I graphArray membershipArray) (command graphArray membershipArray)
      (fun _ τ => Representation G I graphArray membershipArray τ ∧
        τ.vars "test.ok"≤1 ∧ (τ.vars "test.ok"=1 ↔ G.IsIndepSet (I : Set (Fin n))))
      (38*n*n+12) := by
  have hwords : ∀ z∈values G I,z<B := by
    intro z hz
    obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hz
    exact (pair_value_le G I _ _).trans_lt (by omega)
  have hs := NativeZeroScan.command_spec B (values G I) (Representation G I graphArray membershipArray)
    (read graphArray membershipArray) 24 (by rw [values_length]; omega) hwords
    (by simp [read,Com.wvars]) (by simp [read,Com.wvars]) (by simp [read,Com.wvars])
    (by
      rintro σ ⟨hn,hg,hm⟩
      exact ⟨by simpa only [vars_setVar,String.reduceEq,if_false] using hn,hg,hm⟩)
    (by
      rintro σ τ rr ⟨hn,hg,hm⟩
      refine ⟨(rr.frame_var "graph.n" (by decide)).trans hn,?_,?_⟩
      · simpa only [Prefix,rr.frame_arr graphArray (by simp [NativeZeroScan.update,Com.warrs])] using hg
      · simpa only [Prefix,rr.frame_arr membershipArray (by simp [NativeZeroScan.update,Com.warrs])] using hm)
    (read_graph_spec B G I graphArray membershipArray hB)
  intro σ hσ
  let ν := σ.setVar "test.limit" (n*n)
  have hnB : n<B := by omega
  have hnnB : n*n<B := by omega
  have r1 : Run B (.assign "test.limit" (.mul (.var "graph.n") (.var "graph.n"))) σ ν 4 :=
    Run.assign (evalB_bin (op := .mul)
      (by rw [evalB_var_iff]; exact ⟨hσ.1.symm,hσ.1 ▸ hnB⟩)
      (by rw [evalB_var_iff]; exact ⟨hσ.1.symm,hσ.1 ▸ hnB⟩) hnnB)
  have hν : Representation G I graphArray membershipArray ν :=
    ⟨by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hσ.1,hσ.2⟩
  obtain ⟨τ,r2,p2⟩ := hs ν ⟨hν,by simp [ν,values_length]⟩
  refine ⟨τ,(r1.seq r2).mono (by rw [values_length]; nlinarith),p2.1,?_,?_⟩
  · rw [p2.2]
    exact NativeZeroScan.prefix_ok_le _ _
  · rw [p2.2,values_length,values_correct]

end Lax263307Proofs.NativeIndependentTest
