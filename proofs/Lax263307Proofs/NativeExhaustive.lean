import Lax263307.IndependentSetEncoding
import Lax263307.ExhaustiveTargets
import Lax263307.WeightedIndependentSet
import Lax808846.Ram
import Lax263307Proofs.NativeCombinations
import Lax263307Proofs.NativeIndependentTest
import Lax455465Proofs.RamArrayCopy

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeExhaustive

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307.ExhaustiveTargets

def Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "choose.n"=n ∧ σ.vars "choose.cols"=k+1 ∧ σ.vars "target.k"=k ∧
  Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧
  Prefix (NativeCombinations.table n k) "choose.table" σ ∧ n≤(σ.arrs "subset.bits").length

theorem data_frame {n B K : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    (h0 : "graph.n"∉c.wvars) (h1 : "choose.n"∉c.wvars) (h2 : "choose.cols"∉c.wvars)
    (h3 : "target.k"∉c.wvars) (h4 : "search.graph"∉c.warrs) (h5 : "choose.table"∉c.warrs)
    (hσ : Data G k σ) : Data G k τ := by
  rcases hσ with ⟨hn,hcn,hcols,hk,hg,ht,hr⟩
  refine ⟨(rr.frame_var "graph.n" h0).trans hn,(rr.frame_var "choose.n" h1).trans hcn,
    (rr.frame_var "choose.cols" h2).trans hcols,(rr.frame_var "target.k" h3).trans hk,?_,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "search.graph" h4] using hg
  · simpa only [Prefix,rr.frame_arr "choose.table" h5] using ht
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]

def candidate (n k rank : ℕ) : Finset (Fin n) :=
  (NativeCombinations.decode (List.finRange n) (NativeCombinations.bits n k rank)).toFinset

theorem candidate_get (n k rank : ℕ) (hrank : rank<n.choose k) :
    (candidates n k)[rank]?=some (candidate n k rank) :=
  NativeCombinations.candidate_coordinate n k rank hrank

def prepareCandidate : Com := .seq (.assign "subset.need" (.var "target.k"))
  (.assign "subset.rank" (.var "target.i"))

def candidateCommand : Com := .seq prepareCandidate (.seq NativeCombinations.subsetCommand
  (.seq (NativeIndependentTest.command "search.graph" "subset.bits")
    (.assign "target.found" (.var "test.ok"))))

theorem candidate_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k rank : ℕ) (hB : n*n+(n+1)*(k+1)+n+k+5<B) (hrank : rank<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (fun σ => Data G k σ ∧ σ.vars "target.i"=rank) candidateCommand
      (fun _ τ => Data G k τ ∧ Prefix (encodeOutput (candidate n k rank)) "subset.bits" τ ∧
        τ.vars "target.found"≤1 ∧ (τ.vars "target.found"=1 ↔ G.IsIndepSet (candidate n k rank : Set (Fin n))))
      (38*n*n+54*n+24) := by
  have hkB : k<B := by omega
  have hsetup : Spec B (fun σ => σ.vars "target.k"=k ∧ σ.vars "target.i"=rank) prepareCandidate
      (fun _ τ => τ.vars "subset.need"=k ∧ τ.vars "subset.rank"=rank) 4 := by
    run_vcg
    all_goals simp_all [Env.setVar]
  rintro σ ⟨hdata,hrankσ⟩
  obtain ⟨ν,r1,p1⟩ := hsetup σ ⟨hdata.2.2.2.1,hrankσ⟩
  have d1 := data_frame G k r1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hdata
  obtain ⟨μ,r2,p2⟩ := NativeCombinations.subset_command_spec B n k rank (by omega) hrank hcoeff ν
    ⟨d1.2.1,d1.2.2.1,p1.1,p1.2,d1.2.2.2.2.2.1,d1.2.2.2.2.2.2⟩
  have d2 := data_frame G k r2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d1
  have hbits : Prefix (encodeOutput (candidate n k rank)) "subset.bits" μ := by
    rw [NativeCombinations.bits_encoding] at p2
    exact p2
  obtain ⟨ξ,r3,p3⟩ := NativeIndependentTest.command_spec B G (candidate n k rank) "search.graph" "subset.bits"
    (by omega) μ ⟨d2.1,d2.2.2.2.2.1,hbits⟩
  have d3 := data_frame G k r3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d2
  let τ := ξ.setVar "target.found" (ξ.vars "test.ok")
  have r4 : Run B (.assign "target.found" (.var "test.ok")) ξ τ 2 :=
    Run.assign (evalB_var (p3.2.1.trans_lt (by omega)))
  have d4 := data_frame G k r4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d3
  have rtotal := r1.seq (r2.seq (r3.seq r4))
  refine ⟨τ,rtotal.mono (by omega),d4,?_,?_,?_⟩
  · simpa only [Prefix,r4.frame_arr "subset.bits" (by decide)] using p3.1.2.2
  · simpa only [τ,vars_setVar,if_true] using p3.2.1
  · simpa only [τ,vars_setVar,if_true] using p3.2.2

def prefixFind {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k i : ℕ) : Option (Finset (Fin n)) :=
  ((candidates n k).take i).find? fun I => decide (G.IsIndepSet (I : Set (Fin n)))

theorem candidates_length (n k : ℕ) : (candidates n k).length=n.choose k := by
  simp [candidates,List.length_sublistsLen]

theorem prefix_find_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) :
    prefixFind G k 0=none := by simp [prefixFind]

theorem prefix_find_succ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k i : ℕ) (hi : i<n.choose k) :
    prefixFind G k (i+1)=match prefixFind G k i with
      | some I => some I
      | none => if G.IsIndepSet (candidate n k i : Set (Fin n)) then some (candidate n k i) else none := by
  have hic : i<(candidates n k).length := by rwa [candidates_length]
  have hc := candidate_get n k i hi
  rw [List.getElem?_eq_getElem hic] at hc
  have he := Option.some.inj hc
  unfold prefixFind
  rw [List.take_succ_eq_append_getElem hic,he,List.find?_append]
  cases h : ((candidates n k).take i).find? (fun (I : Finset (Fin n)) => decide (G.IsIndepSet (I : Set (Fin n)))) <;> simp

def Result {n : ℕ} (answer : Option (Finset (Fin n))) (σ : Env) : Prop :=
  match answer with
  | none => σ.vars "target.found"=0
  | some I => σ.vars "target.found"=1 ∧ Prefix (encodeOutput I) "subset.bits" σ

def Invariant {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (σ : Env) : Prop :=
  Data G k σ ∧ σ.vars "target.count"=n.choose k ∧ σ.vars "target.i"≤n.choose k ∧
    Result (prefixFind G k (σ.vars "target.i")) σ

def step : Com := .seq (.ite (.eq (.var "target.found") (.lit 0)) candidateCommand .skip)
  (.assign "target.i" (.add (.var "target.i") (.lit 1)))

theorem step_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hB : n*n+(n+1)*(k+1)+n+k+5<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (fun σ => Invariant G k σ ∧ σ.vars "target.i"<n.choose k) step
      (fun σ τ => Invariant G k τ ∧ τ.vars "target.i"=σ.vars "target.i"+1)
      (38*n*n+54*n+40) := by
  rintro σ ⟨⟨hdata,hcount,hle,hresult⟩,hlt⟩
  let i := σ.vars "target.i"
  have hcountB := hcoeff n le_rfl k le_rfl
  have hiB : i<B := hlt.trans hcountB
  have hi1B : i+1<B := by dsimp [i]; omega
  have h0 : 0<B := by omega
  have h1 : 1<B := by omega
  change Result (prefixFind G k i) σ at hresult
  cases hf : prefixFind G k i with
  | none =>
    have hfound : σ.vars "target.found"=0 := by simpa only [hf,Result] using hresult
    obtain ⟨ν,r1,p1⟩ := candidate_spec B G k i hB hiB hcoeff σ ⟨hdata,rfl⟩
    have hb : (Cond.eq (.var "target.found") (.lit 0)).evalB B σ=some true :=
      evalB_condEq (by rw [evalB_var_iff]; exact ⟨hfound.symm,hfound ▸ h0⟩) (evalB_lit h0)
    have rb : Run B (.ite (.eq (.var "target.found") (.lit 0)) candidateCommand .skip) σ ν
        (4+(38*n*n+54*n+24)) := Run.ite_true hb r1
    have hiν : ν.vars "target.i"=i := r1.frame_var "target.i" (by decide)
    let τ := ν.setVar "target.i" (i+1)
    have r2 : Run B (.assign "target.i" (.add (.var "target.i") (.lit 1))) ν τ 4 :=
      Run.assign (evalB_bin (op := .add)
        (by rw [evalB_var_iff]; exact ⟨hiν.symm,hiν ▸ hiB⟩) (evalB_lit h1) hi1B)
    have rr := rb.seq r2
    have ht : τ.vars "target.i"=i+1 := by simp [τ]
    have hd := data_frame G k r2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) p1.1
    refine ⟨τ,rr.mono (by omega),⟨hd,?_,by rw [ht]; omega,?_⟩,ht⟩
    · exact (rr.frame_var "target.count" (by decide)).trans hcount
    · rw [ht,prefix_find_succ G k i hlt,hf]
      dsimp only
      by_cases hgood : G.IsIndepSet (candidate n k i : Set (Fin n))
      · rw [if_pos hgood]
        refine ⟨?_,?_⟩
        · exact (r2.frame_var "target.found" (by decide)).trans (p1.2.2.2.mpr hgood)
        · simpa only [Prefix,r2.frame_arr "subset.bits" (by decide)] using p1.2.1
      · rw [if_neg hgood]
        have hnot : ν.vars "target.found"≠1 := mt p1.2.2.2.mp hgood
        have hz : ν.vars "target.found"=0 := by have hh := p1.2.2.1; omega
        exact (r2.frame_var "target.found" (by decide)).trans hz
  | some I =>
    have hfound : σ.vars "target.found"=1 ∧ Prefix (encodeOutput I) "subset.bits" σ := by
      simpa only [hf,Result] using hresult
    have hb : (Cond.eq (.var "target.found") (.lit 0)).evalB B σ=some false :=
      evalB_condEq (by rw [evalB_var_iff]; exact ⟨hfound.1.symm,hfound.1 ▸ h1⟩) (evalB_lit h0)
    have rb : Run B (.ite (.eq (.var "target.found") (.lit 0)) candidateCommand .skip) σ σ 5 :=
      Run.ite_false hb Run.skip
    let τ := σ.setVar "target.i" (i+1)
    have r2 : Run B (.assign "target.i" (.add (.var "target.i") (.lit 1))) σ τ 4 :=
      Run.assign (evalB_bin (op := .add) (evalB_var hiB) (evalB_lit h1) hi1B)
    have rr := rb.seq r2
    have ht : τ.vars "target.i"=i+1 := by simp [τ]
    have hd := data_frame G k r2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hdata
    refine ⟨τ,rr.mono (by omega),⟨hd,?_,by rw [ht]; omega,?_⟩,ht⟩
    · exact (r2.frame_var "target.count" (by decide)).trans hcount
    · rw [ht,prefix_find_succ G k i hlt,hf]
      refine ⟨(r2.frame_var "target.found" (by decide)).trans hfound.1,?_⟩
      simpa only [Prefix,r2.frame_arr "subset.bits" (by decide)] using hfound.2

def search : Com := .seq (.assign "target.found" (.lit 0))
  (.seq (.assign "target.i" (.lit 0))
    (.while (.lt (.var "target.i") (.var "target.count")) step))

theorem search_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hB : n*n+(n+1)*(k+1)+n+k+5<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (fun σ => Data G k σ ∧ σ.vars "target.count"=n.choose k) search
      (fun _ τ => Data G k τ ∧ Result (findIndependentSet G k) τ)
      ((38*n*n+54*n+44)*(n.choose k)+8) := by
  have hloop := Spec.forRangeZero "target.i" "target.count" (Invariant G k) (n.choose k)
    (38*n*n+54*n+40) (hcoeff n le_rfl k le_rfl)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1) (step_spec B G k hB hcoeff)
  rintro σ ⟨hdata,hcount⟩
  let ν := σ.setVar "target.found" 0
  have r1 : Run B (.assign "target.found" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hi : Invariant G k (ν.setVar "target.i" 0) := by
    refine ⟨?_,?_,by simp,?_⟩
    · simpa only [Data,ν,vars_setVar,String.reduceEq,if_false,Prefix,arrs_setVar] using hdata
    · simpa only [ν,vars_setVar,String.reduceEq,if_false] using hcount
    · simp [ν,prefix_find_zero,Result]
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by nlinarith),p2.1.1,?_⟩
  have he : prefixFind G k (n.choose k)=findIndependentSet G k := by
    unfold prefixFind findIndependentSet
    rw [List.take_of_length_le (by rw [candidates_length])]
  simpa only [p2.2,he] using p2.1.2.2.2

def setup : Com := .seq (.assign "choose.n" (.var "graph.n"))
  (.assign "choose.k" (.var "target.k"))

def readCount : Com := .assign "target.count" (.get "choose.table"
  (.add (.mul (.var "graph.n") (.var "choose.cols")) (.var "target.k")))

def prepare : Com := .seq setup (.seq NativeCombinations.command readCount)

def Input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "target.k"=k ∧
  Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧
  (n+1)*(k+1)≤(σ.arrs "choose.table").length ∧ n≤(σ.arrs "subset.bits").length

theorem prepare_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hB : n*n+(n+1)*(k+1)+n+k+5<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (Input G k) prepare (fun _ τ => Data G k τ ∧ τ.vars "target.count"=n.choose k)
      (54*(n+1)*(k+1)+27) := by
  have hnB : n<B := by omega
  have hkB : k<B := by omega
  have hcolsB : k+1<B := by omega
  have hsetup : Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "target.k"=k) setup
      (fun _ τ => τ.vars "choose.n"=n ∧ τ.vars "choose.k"=k) 4 := by
    run_vcg
    all_goals simp_all [Env.setVar]
  rintro σ ⟨hn,hk,hgraph,htableroom,hbitsroom⟩
  obtain ⟨ν,r1,p1⟩ := hsetup σ ⟨hn,hk⟩
  obtain ⟨μ,r2,p2⟩ := NativeCombinations.command_spec B n k (by omega) hcoeff ν
    ⟨p1.1,p1.2,by rwa [Lax455465Proofs.RamFrames.run_array_length r1]⟩
  have r12 := r1.seq r2
  have d2 : Data G k μ := by
    refine ⟨(r12.frame_var "graph.n" (by decide)).trans hn,
      (r2.frame_var "choose.n" (by decide)).trans p1.1,p2.2,
      (r12.frame_var "target.k" (by decide)).trans hk,?_,p2.1,?_⟩
    · simpa only [Prefix,r12.frame_arr "search.graph" (by decide)] using hgraph
    · rwa [Lax455465Proofs.RamFrames.run_array_length r12]
  have hidx : n*(k+1)+k<(NativeCombinations.table n k).length := by
    rw [NativeCombinations.table_length]
    nlinarith
  have hc := NativeCombinations.table_coordinate n k n k le_rfl le_rfl
  rw [List.getElem?_eq_getElem hidx] at hc
  have hget := (p2.1 (n*(k+1)+k) hidx).trans hc
  have hidxB : n*(k+1)+k<B := by rw [NativeCombinations.table_length] at hidx; omega
  have hmulB : n*(k+1)<B := by omega
  have hindex : (Expr.add (.mul (.var "graph.n") (.var "choose.cols")) (.var "target.k")).evalB B μ=
      some (n*(k+1)+k) := evalB_bin (op := .add)
    (evalB_bin (op := .mul)
      (by rw [evalB_var_iff]; exact ⟨d2.1.symm,d2.1 ▸ hnB⟩)
      (by rw [evalB_var_iff]; exact ⟨d2.2.2.1.symm,d2.2.2.1 ▸ hcolsB⟩) hmulB)
    (by rw [evalB_var_iff]; exact ⟨d2.2.2.2.1.symm,d2.2.2.2.1 ▸ hkB⟩) hidxB
  let τ := μ.setVar "target.count" (n.choose k)
  have r3 : Run B readCount μ τ 7 := Run.assign (evalB_get hindex hget (hcoeff n le_rfl k le_rfl))
  have d3 := data_frame G k r3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) d2
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),d3,?_⟩
  simp [τ]

def command : Com := .seq prepare search

def cost (n k : ℕ) : ℕ := 54*(n+1)*(k+1)+(38*n*n+54*n+44)*(n.choose k)+35

theorem command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ) (hB : n*n+(n+1)*(k+1)+n+k+5<B)
    (hcoeff : ∀ i≤n,∀ j≤k,i.choose j<B) :
    Spec B (Input G k) command (fun _ τ => Result (findIndependentSet G k) τ) (cost n k) := by
  intro σ hσ
  obtain ⟨ν,r1,p1⟩ := prepare_spec B G k hB hcoeff σ hσ
  obtain ⟨τ,r2,p2⟩ := search_spec B G k hB hcoeff ν p1
  exact ⟨τ,(r1.seq r2).mono (by dsimp [cost]; omega),p2.2⟩

def encodeInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : List ℕ :=
  n::k::(n*n)::NativeWeightReduction.adjacency G

def encodeAnswer {n : ℕ} : Option (Finset (Fin n)) → List ℕ
  | none => [0]
  | some I => 1::encodeOutput I

def readInput : Com := .seq (.read "graph.n") (.seq (.read "target.k")
  (.seq Lax455465Proofs.RamInputCopy.copy
    (Lax455465Proofs.RamArrayCopy.command "input.data" "search.graph" "input.length")))

theorem adjacency_words {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∀ z∈NativeWeightReduction.adjacency G,z≤1 := by
  intro z hz
  obtain ⟨r,hr,hz⟩ := List.mem_flatten.mp hz
  obtain ⟨u,rfl⟩ := List.mem_ofFn.mp hr
  obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hz
  split_ifs <;> omega


def emit : Com := .seq (.write (.var "target.found"))
  (.ite (.eq (.var "target.found") (.lit 1))
    (.seq (.assign "emit.count" (.var "graph.n")) (Lax455465Proofs.RamEmitWords.command "subset.bits" 1)) .skip)


def fullCommand : Com := .seq readInput (.seq command emit)

def totalCost (n k : ℕ) : ℕ := cost n k+24*n*n+13*n+29


open Lax109476Proofs

def layout := RamAutomaticLayout.layout fullCommand
def program : Lax808846.Ram.Program := Lax808846Proofs.Compile.compileProgram layout fullCommand


end Lax263307Proofs.NativeExhaustive
