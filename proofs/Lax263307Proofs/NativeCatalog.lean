import Lax263307Proofs.NativeMasks
import Lax263307Proofs.NativeCatalogOrder

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeCatalog

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet
open Lax263307

def block (n k : ℕ) : List ℕ :=
  (ExhaustiveTargets.candidates n k).map NativeMasks.mask

theorem block_length (n k : ℕ) : (block n k).length=n.choose k := by
  simp only [block,List.length_map,NativeExhaustive.candidates_length]

theorem block_entry (n k i : ℕ) (hi : i<n.choose k) :
    (block n k)[i]?=some (NativeMasks.mask (NativeExhaustive.candidate n k i)) := by
  rw [block,List.getElem?_map,NativeExhaustive.candidate_get n k i hi]
  rfl

def Data (n k : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "choose.n"=n ∧ σ.vars "choose.cols"=k+1 ∧
  σ.vars "catalog.k"=k ∧ Prefix (NativeCombinations.table n k) "choose.table" σ ∧
  n≤(σ.arrs "subset.bits").length

theorem data_frame {B n k K : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    (h0 : "graph.n"∉c.wvars) (h1 : "choose.n"∉c.wvars) (h2 : "choose.cols"∉c.wvars)
    (h3 : "catalog.k"∉c.wvars) (h4 : "choose.table"∉c.warrs)
    (hσ : Data n k σ) : Data n k τ := by
  rcases hσ with ⟨hn,hcn,hcols,hk,ht,hr⟩
  refine ⟨(rr.frame_var "graph.n" h0).trans hn,(rr.frame_var "choose.n" h1).trans hcn,
    (rr.frame_var "choose.cols" h2).trans hcols,(rr.frame_var "catalog.k" h3).trans hk,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "choose.table" h4] using ht
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]

def prepareCandidate : Com := .seq (.assign "subset.need" (.var "catalog.k"))
  (.assign "subset.rank" (.var "catalog.i"))

def candidateCommand : Com := .seq prepareCandidate (.seq NativeCombinations.subsetCommand NativeMasks.command)

theorem candidate_spec (B n k i : ℕ) (hB : (n+1)*(k+1)+n+k+3<B) (hi : i<B)
    (hm : 2^n<B) (hcoeff : ∀ a≤n,∀ b≤k,a.choose b<B) :
    Spec B (fun σ => Data n k σ ∧ σ.vars "catalog.i"=i) candidateCommand
      (fun _ τ => Data n k τ ∧ τ.vars "mask.value"=NativeMasks.mask (NativeExhaustive.candidate n k i))
      (69*n+18) := by
  have hsetup : Spec B (fun σ => σ.vars "catalog.k"=k ∧ σ.vars "catalog.i"=i) prepareCandidate
      (fun _ τ => τ.vars "subset.need"=k ∧ τ.vars "subset.rank"=i) 4 := by
    run_vcg
    all_goals simp_all [Env.setVar]
  rintro σ ⟨hd,hiσ⟩
  obtain ⟨ν,r1,p1⟩ := hsetup σ ⟨hd.2.2.2.1,hiσ⟩
  have d1 := data_frame r1 (by decide) (by decide) (by decide) (by decide) (by decide) hd
  obtain ⟨μ,r2,p2⟩ := NativeCombinations.subset_command_spec B n k i hB hi hcoeff ν
    ⟨d1.2.1,d1.2.2.1,p1.1,p1.2,d1.2.2.2.2.1,d1.2.2.2.2.2⟩
  have d2 := data_frame r2 (by decide) (by decide) (by decide) (by decide) (by decide) d1
  have hb : Prefix (encodeOutput (NativeExhaustive.candidate n k i)) "subset.bits" μ := by
    rw [NativeCombinations.bits_encoding] at p2
    exact p2
  obtain ⟨τ,r3,p3⟩ := NativeMasks.command_spec B (NativeExhaustive.candidate n k i) (by omega) hm μ ⟨d2.1,hb⟩
  have d3 := data_frame r3 (by decide) (by decide) (by decide) (by decide) (by decide) d2
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),d3,p3⟩

def BlockInvariant (n k : ℕ) (before : List ℕ) (σ : Env) : Prop :=
  Data n k σ ∧ σ.vars "catalog.blockLength"=n.choose k ∧ σ.vars "catalog.i"≤n.choose k ∧
  σ.vars "catalog.count"=before.length+σ.vars "catalog.i" ∧
  before.length+n.choose k≤(σ.arrs "catalog.mask").length ∧
  Prefix (before++(block n k).take (σ.vars "catalog.i")) "catalog.mask" σ

def blockStep : Com := .seq candidateCommand
  (.seq (Lax455465Proofs.RamWordBuffer.append "catalog.mask" "catalog.count" (.var "mask.value"))
    (.assign "catalog.i" (.add (.var "catalog.i") (.lit 1))))

theorem block_step_spec (B n k : ℕ) (before : List ℕ)
    (hB : (n+1)*(k+1)+n+k+3<B) (hm : 2^n<B)
    (hsize : before.length+n.choose k+1<B) (hcoeff : ∀ a≤n,∀ b≤k,a.choose b<B) :
    Spec B (fun σ => BlockInvariant n k before σ ∧ σ.vars "catalog.i"<n.choose k) blockStep
      (fun σ τ => BlockInvariant n k before τ ∧ τ.vars "catalog.i"=σ.vars "catalog.i"+1)
      (69*n+29) := by
  rintro σ ⟨⟨hd,hlimit,hle,hcount,hroom,hprefix⟩,hlt⟩
  let i := σ.vars "catalog.i"
  have hiB : i<B := hlt.trans (hcoeff n le_rfl k le_rfl)
  have hlen : (before++(block n k).take i).length=before.length+i := by
    rw [List.length_append,List.length_take,block_length,Nat.min_eq_left (by omega)]
  have hval := block_entry n k i hlt
  have hib : i<(block n k).length := by rwa [block_length]
  rw [List.getElem?_eq_getElem hib] at hval
  have hv := Option.some.inj hval
  obtain ⟨ν,r1,p1⟩ := candidate_spec B n k i hB hiB hm hcoeff σ ⟨hd,rfl⟩
  have hiν : ν.vars "catalog.i"=i := r1.frame_var "catalog.i" (by decide)
  have hcν : ν.vars "catalog.count"=before.length+i :=
    (r1.frame_var "catalog.count" (by decide)).trans hcount
  obtain ⟨μ,r2,p2⟩ := Lax455465Proofs.RamWordBuffer.append_spec B "catalog.mask" "catalog.count"
    (before++(block n k).take i) (NativeMasks.mask (NativeExhaustive.candidate n k i))
    (.var "mask.value") (by omega) (by rw [hlen]; omega) ν
    ⟨by simpa only [Prefix,r1.frame_arr "catalog.mask" (by decide)] using hprefix,
      by rwa [hlen],by rw [hlen,Lax455465Proofs.RamFrames.run_array_length r1]; omega,
      by rw [evalB_var_iff]; exact ⟨p1.2.symm,p1.2 ▸ (NativeMasks.mask_bound _).trans hm⟩⟩
  have hiμ : μ.vars "catalog.i"=i := (r2.frame_var "catalog.i" (by decide)).trans hiν
  let τ := μ.setVar "catalog.i" (i+1)
  have r3 : Run B (.assign "catalog.i" (.add (.var "catalog.i") (.lit 1))) μ τ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ hiB⟩) (evalB_lit (by omega))
      (by change i+1<B; omega))
  have rr := r1.seq (r2.seq r3)
  have ht : τ.vars "catalog.i"=i+1 := by simp [τ]
  refine ⟨τ,rr.mono (by simp only [Expr.size]; omega),?_,ht⟩
  refine ⟨data_frame rr (by decide) (by decide) (by decide) (by decide) (by decide) hd,
    (rr.frame_var "catalog.blockLength" (by decide)).trans hlimit,by rw [ht]; omega,?_,?_,?_⟩
  · rw [ht]
    have hc := (r3.frame_var "catalog.count" (by decide)).trans p2.2
    rw [hlen] at hc
    exact hc
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
  · rw [ht,List.take_succ_eq_append_getElem hib,hv,←List.append_assoc]
    simpa only [Prefix,r3.frame_arr "catalog.mask" (by decide)] using p2.1

def blockCommand : Com := .seq (.assign "catalog.i" (.lit 0))
  (.while (.lt (.var "catalog.i") (.var "catalog.blockLength")) blockStep)

theorem block_command_spec (B n k : ℕ) (before : List ℕ)
    (hB : (n+1)*(k+1)+n+k+3<B) (hm : 2^n<B)
    (hsize : before.length+n.choose k+1<B) (hcoeff : ∀ a≤n,∀ b≤k,a.choose b<B) :
    Spec B (fun σ => Data n k σ ∧ σ.vars "catalog.blockLength"=n.choose k ∧
      σ.vars "catalog.count"=before.length ∧ before.length+n.choose k≤(σ.arrs "catalog.mask").length ∧
      Prefix before "catalog.mask" σ) blockCommand
      (fun _ τ => Data n k τ ∧ τ.vars "catalog.count"=before.length+n.choose k ∧ Prefix (before++block n k) "catalog.mask" τ)
      ((69*n+33)*(n.choose k)+6) := by
  have hloop := Spec.forRangeZero "catalog.i" "catalog.blockLength" (BlockInvariant n k before)
    (n.choose k) (69*n+29) (hcoeff n le_rfl k le_rfl)
    (fun _ h => h.2.2.1) (fun _ h => h.2.1)
    (block_step_spec B n k before hB hm hsize hcoeff)
  rintro σ ⟨hd,hlimit,hcount,hroom,hprefix⟩
  have hi : BlockInvariant n k before (σ.setVar "catalog.i" 0) := by
    refine ⟨?_,?_,by simp,?_,hroom,?_⟩
    · simpa [Data,Prefix] using hd
    · simpa only [vars_setVar,String.reduceEq,if_false] using hlimit
    · simpa only [vars_setVar,String.reduceEq,if_true,if_false,Nat.add_zero] using hcount
    · simpa only [Prefix,arrs_setVar,vars_setVar,if_true,List.take_zero,List.append_nil] using hprefix
  obtain ⟨τ,rr,p⟩ := hloop σ hi
  refine ⟨τ,rr,p.1.1,?_,?_⟩
  · simpa only [p.2] using p.1.2.2.2.1
  · have htake : (block n k).take (n.choose k)=block n k :=
      List.take_of_length_le (by rw [block_length])
    simpa only [p.2,htake] using p.1.2.2.2.2.2

def prepare : Com := .seq
  (.seq (.assign "choose.n" (.var "graph.n")) (.assign "choose.k" (.var "catalog.k")))
  (.seq NativeCombinations.command (.assign "catalog.blockLength"
    (.get "choose.table" (.add (.mul (.var "choose.n") (.var "choose.cols")) (.var "catalog.k")))))

theorem prepare_spec (B n k : ℕ) (hB : (n+1)*(k+1)+n+k+3<B)
    (hcoeff : ∀ a≤n,∀ b≤k,a.choose b<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "catalog.k"=k ∧
      (n+1)*(k+1)≤(σ.arrs "choose.table").length ∧ n≤(σ.arrs "subset.bits").length) prepare
      (fun _ τ => Data n k τ ∧ τ.vars "catalog.blockLength"=n.choose k)
      (54*(n+1)*(k+1)+27) := by
  have hsetup : Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "catalog.k"=k)
      (.seq (.assign "choose.n" (.var "graph.n")) (.assign "choose.k" (.var "catalog.k")))
      (fun _ τ => τ.vars "choose.n"=n ∧ τ.vars "choose.k"=k) 4 := by
    run_vcg
    all_goals simp_all [Env.setVar]
  rintro σ ⟨hn,hk,hroom,hbits⟩
  obtain ⟨ν,r1,p1⟩ := hsetup σ ⟨hn,hk⟩
  obtain ⟨μ,r2,p2⟩ := NativeCombinations.command_spec B n k hB hcoeff ν
    ⟨p1.1,p1.2,by rwa [Lax455465Proofs.RamFrames.run_array_length r1]⟩
  have r12 := r1.seq r2
  have hcn : μ.vars "choose.n"=n := (r2.frame_var "choose.n" (by decide)).trans p1.1
  have hkμ : μ.vars "catalog.k"=k := (r12.frame_var "catalog.k" (by decide)).trans hk
  have hindex : n*(k+1)+k<(NativeCombinations.table n k).length := by
    rw [NativeCombinations.table_length]
    nlinarith
  have hget := p2.1 (n*(k+1)+k) hindex
  have he := NativeCombinations.table_coordinate n k n k le_rfl le_rfl
  rw [List.getElem?_eq_getElem hindex] at he
  rw [Option.some.inj he] at hget
  have hval : (Expr.get "choose.table"
      (.add (.mul (.var "choose.n") (.var "choose.cols")) (.var "catalog.k"))).evalB B μ=some (n.choose k) := by
    apply evalB_get _ hget (hcoeff n le_rfl k le_rfl)
    apply evalB_bin (op := .add) _ _ (by change n*(k+1)+k<B; nlinarith)
    · apply evalB_bin (op := .mul) _ _ (by change n*(k+1)<B; nlinarith)
      · rw [evalB_var_iff]; exact ⟨hcn.symm,hcn ▸ (by omega)⟩
      · rw [evalB_var_iff]; exact ⟨p2.2.symm,p2.2 ▸ (by omega)⟩
    · rw [evalB_var_iff]; exact ⟨hkμ.symm,hkμ ▸ (by omega)⟩
  let τ := μ.setVar "catalog.blockLength" (n.choose k)
  have r3 : Run B (.assign "catalog.blockLength" (.get "choose.table"
      (.add (.mul (.var "choose.n") (.var "choose.cols")) (.var "catalog.k")))) μ τ 7 := Run.assign hval
  have rr := r1.seq (r2.seq r3)
  refine ⟨τ,rr.mono (by omega),?_,by simp [τ]⟩
  refine ⟨(rr.frame_var "graph.n" (by decide)).trans hn,
    (r3.frame_var "choose.n" (by decide)).trans hcn,
    (r3.frame_var "choose.cols" (by decide)).trans p2.2,
    (rr.frame_var "catalog.k" (by decide)).trans hk,?_,?_⟩
  · simpa only [Prefix,r3.frame_arr "choose.table" (by decide)] using p2.1
  · rwa [Lax455465Proofs.RamFrames.run_array_length rr]

def rows (n q : ℕ) : List ℕ := (List.range q).flatMap (block n)

theorem rows_zero (n : ℕ) : rows n 0=[] := rfl

theorem rows_succ (n q : ℕ) : rows n (q+1)=rows n q++block n q := by
  simp only [rows,List.range_succ,List.flatMap_append,List.flatMap_singleton]

theorem rows_length_mono (n : ℕ) : Monotone (fun q => (rows n q).length) := by
  apply monotone_nat_of_le_succ
  intro q
  rw [rows_succ,List.length_append]
  omega

theorem rows_length_step (n q : ℕ) : (rows n (q+1)).length=(rows n q).length+n.choose q := by
  rw [rows_succ,List.length_append,block_length]

theorem rows_exact (n r : ℕ) : rows n (r+3)=
    (CoordinateCatalog.catalog n r).map (fun A => NativeMasks.mask A.val) := by
  change rows n (r+3)=(CoordinateCatalog.catalog n r).map (NativeMasks.mask ∘ Subtype.val)
  rw [←List.map_map,NativeCatalogOrder.catalog_values]
  simp only [rows,RationalConditioning.candidates,List.map_flatMap]
  rfl

def OuterData (n R : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "catalog.limit"=R+1 ∧
  (n+1)*(R+1)≤(σ.arrs "choose.table").length ∧ n≤(σ.arrs "subset.bits").length ∧
  (rows n (R+1)).length≤(σ.arrs "catalog.mask").length

theorem outer_data_frame {B n R K : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K)
    (h0 : "graph.n"∉c.wvars) (h1 : "catalog.limit"∉c.wvars)
    (hσ : OuterData n R σ) : OuterData n R τ := by
  rcases hσ with ⟨hn,hl,ht,hb,hr⟩
  refine ⟨(rr.frame_var "graph.n" h0).trans hn,(rr.frame_var "catalog.limit" h1).trans hl,?_,?_,?_⟩
  all_goals rwa [Lax455465Proofs.RamFrames.run_array_length rr]

def OuterInvariant (n R : ℕ) (σ : Env) : Prop :=
  OuterData n R σ ∧ σ.vars "catalog.k"≤R+1 ∧
  σ.vars "catalog.count"=(rows n (σ.vars "catalog.k")).length ∧
  Prefix (rows n (σ.vars "catalog.k")) "catalog.mask" σ

def outerStep : Com := .seq prepare (.seq blockCommand
  (.assign "catalog.k" (.add (.var "catalog.k") (.lit 1))))

theorem outer_step_spec (B n R : ℕ) (hB : (n+1)*(R+1)+n+R+3<B) (hm : 2^n<B)
    (hsize : (rows n (R+1)).length+1<B) (hcoeff : ∀ a≤n,∀ b≤R,a.choose b<B) :
    Spec B (fun σ => OuterInvariant n R σ ∧ σ.vars "catalog.k"<R+1) outerStep
      (fun σ τ => OuterInvariant n R τ ∧ τ.vars "catalog.k"=σ.vars "catalog.k"+1)
      (54*(n+1)*(R+1)+(69*n+33)*(rows n (R+1)).length+37) := by
  rintro σ ⟨⟨hd,hle,hcount,hprefix⟩,hlt⟩
  let k := σ.vars "catalog.k"
  have hk : k≤R := by omega
  have htable : (n+1)*(k+1)≤(n+1)*(R+1) := Nat.mul_le_mul_left _ (by omega)
  have hb : (n+1)*(k+1)+n+k+3<B := by omega
  have hc : ∀ a≤n,∀ b≤k,a.choose b<B := fun a ha b hbk => hcoeff a ha b (hbk.trans hk)
  have hrows := rows_length_mono n (show k+1≤R+1 by omega)
  have hroom : (rows n k).length+n.choose k≤(rows n (R+1)).length := by
    simpa only [rows_length_step] using hrows
  obtain ⟨ν,r1,p1⟩ := prepare_spec B n k hb hc σ ⟨hd.1,rfl,htable.trans hd.2.2.1,hd.2.2.2.1⟩
  have d1 := outer_data_frame r1 (by decide) (by decide) hd
  have hkν : ν.vars "catalog.k"=k := r1.frame_var "catalog.k" (by decide)
  obtain ⟨μ,r2,p2⟩ := block_command_spec B n k (rows n k) hb hm (by omega) hc ν
    ⟨p1.1,p1.2,(r1.frame_var "catalog.count" (by decide)).trans hcount,
      hroom.trans d1.2.2.2.2,
      by simpa only [Prefix,r1.frame_arr "catalog.mask" (by decide)] using hprefix⟩
  have hkμ : μ.vars "catalog.k"=k := (r2.frame_var "catalog.k" (by decide)).trans hkν
  let τ := μ.setVar "catalog.k" (k+1)
  have r3 : Run B (.assign "catalog.k" (.add (.var "catalog.k") (.lit 1))) μ τ 4 :=
    Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hkμ.symm,hkμ ▸ (by omega)⟩) (evalB_lit (by omega))
      (by change k+1<B; omega))
  have rr := r1.seq (r2.seq r3)
  have ht : τ.vars "catalog.k"=k+1 := by simp [τ]
  refine ⟨τ,rr.mono ?_,?_,ht⟩
  · have h1 := Nat.mul_le_mul_left 54 htable
    have h2 := Nat.mul_le_mul_left (69*n+33) (show n.choose k≤(rows n (R+1)).length by omega)
    nlinarith
  · refine ⟨outer_data_frame rr (by decide) (by decide) hd,by rw [ht]; omega,?_,?_⟩
    · rw [ht,rows_length_step]
      exact (r3.frame_var "catalog.count" (by decide)).trans p2.2.1
    · rw [ht,rows_succ]
      simpa only [Prefix,r3.frame_arr "catalog.mask" (by decide)] using p2.2.2

def command : Com := .seq (.assign "catalog.count" (.lit 0))
  (.seq (.assign "catalog.k" (.lit 0)) (.while (.lt (.var "catalog.k") (.var "catalog.limit")) outerStep))

theorem command_spec (B n R : ℕ) (hB : (n+1)*(R+1)+n+R+3<B) (hm : 2^n<B)
    (hsize : (rows n (R+1)).length+1<B) (hcoeff : ∀ a≤n,∀ b≤R,a.choose b<B) :
    Spec B (OuterData n R) command
      (fun _ τ => OuterData n R τ ∧ τ.vars "catalog.count"=(rows n (R+1)).length ∧
        Prefix (rows n (R+1)) "catalog.mask" τ)
      ((54*(n+1)*(R+1)+(69*n+33)*(rows n (R+1)).length+41)*(R+1)+8) := by
  have hloop := Spec.forRangeZero "catalog.k" "catalog.limit" (OuterInvariant n R)
    (R+1) (54*(n+1)*(R+1)+(69*n+33)*(rows n (R+1)).length+37) (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.2.1) (outer_step_spec B n R hB hm hsize hcoeff)
  rintro σ hd
  let ν := σ.setVar "catalog.count" 0
  have r1 : Run B (.assign "catalog.count" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hi : OuterInvariant n R (ν.setVar "catalog.k" 0) := by
    refine ⟨?_,by simp,?_,?_⟩
    · simpa [ν,OuterData] using hd
    · simp [ν,rows_zero]
    · simp only [vars_setVar,if_true,rows_zero,Prefix,List.length_nil]
      intro i hi
      omega
  obtain ⟨τ,r2,p2⟩ := hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by nlinarith),p2.1.1,?_,?_⟩
  · simpa only [p2.2] using p2.1.2.2.1
  · simpa only [p2.2] using p2.1.2.2.2

theorem rows_words (n r : ℕ) : rows n (r+3)=Lax263307.NativeCatalog.words n r := rows_exact n r

theorem rows_positive (n R : ℕ) : 1≤(rows n (R+1)).length := by
  have h := rows_length_mono n (show 1≤R+1 by omega)
  have h1 : (rows n 1).length=1 := by
    rw [show 1=0+1 from rfl,rows_length_step,rows_zero]
    simp
  simpa only [h1] using h

theorem coefficient_bound (n R a b : ℕ) (ha : a≤n) (hb : b≤R) :
    a.choose b≤(rows n (R+1)).length := by
  have h := rows_length_mono n (Nat.add_le_add_right hb 1)
  have hh : (rows n b).length+n.choose b≤(rows n (R+1)).length := by
    simpa only [rows_length_step] using h
  exact (Nat.choose_le_choose b ha).trans (by omega)

theorem rows_values (n R : ℕ) : ∀ z∈rows n (R+1),z<2^n := by
  intro z hz
  obtain ⟨k,hk,hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨I,hI,rfl⟩ := List.mem_map.mp hz
  exact NativeMasks.mask_bound I

def readInput : Com := .seq (.read "graph.n") (.seq (.read "catalog.r")
  (.assign "catalog.limit" (.add (.var "catalog.r") (.lit 3))))

theorem read_input_spec (B n r : ℕ) (hB : n+r+4<B) :
    Spec B (fun σ => σ.inp=[n,r]) readInput
      (fun _ τ => τ.vars "graph.n"=n ∧ τ.vars "catalog.limit"=r+3) 6 := by
  intro σ hinp
  let ν := {σ.setVar "graph.n" n with inp:=[r]}
  have r1 : Run B (.read "graph.n") σ ν 1 := Run.read hinp
  let μ := {ν.setVar "catalog.r" r with inp:=[]}
  have r2 : Run B (.read "catalog.r") ν μ 1 := Run.read rfl
  let τ := μ.setVar "catalog.limit" (r+3)
  have r3 : Run B (.assign "catalog.limit" (.add (.var "catalog.r") (.lit 3))) μ τ 4 :=
    Run.assign (evalB_bin (op := .add) (by simpa [μ] using evalB_var (σ:=μ) (x:="catalog.r") (show μ.vars "catalog.r"<B by simp [μ]; omega))
      (evalB_lit (by omega)) (by change r+3<B; omega))
  exact ⟨τ,r1.seq (r2.seq r3),by simp [τ,μ,ν],by simp [τ]⟩

def emit : Com := .seq (.assign "emit.count" (.var "catalog.count"))
  (Lax455465Proofs.RamEmitWords.command "catalog.mask" 1)

theorem emit_spec (B n R : ℕ) (h1 : 1<B) (hsize : (rows n (R+1)).length<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "catalog.count"=(rows n (R+1)).length ∧ Prefix (rows n (R+1)) "catalog.mask" σ)
      emit (fun σ τ => τ.out=σ.out++rows n (R+1)) (13*(rows n (R+1)).length+8) := by
  rintro σ ⟨hcount,hprefix⟩
  let ν := σ.setVar "emit.count" (rows n (R+1)).length
  have r1 : Run B (.assign "emit.count" (.var "catalog.count")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hcount.symm,hcount ▸ hsize⟩)
  obtain ⟨τ,r2,p2⟩ := Lax455465Proofs.RamEmitWords.command_spec B "catalog.mask" 1
    (rows n (R+1)) σ.out h1 h1 (by simpa using hsize) hsize
    (fun z hz => (rows_values n R z hz).trans hm) ν
    ⟨by simpa only [Lax455465Proofs.RamEmitWords.Data,Prefix,one_mul,ν,arrs_setVar] using hprefix,
      by simp [ν],rfl⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),p2⟩

def fullCommand : Com := .seq readInput (.seq command emit)

def totalCost (n r : ℕ) : ℕ :=
  (54*(n+1)*(r+3)+(69*n+33)*(rows n (r+3)).length+41)*(r+3)+13*(rows n (r+3)).length+22

theorem full_command_spec (B n r : ℕ) (hB : (n+1)*(r+3)+n+r+5<B) (hm : 2^n<B)
    (hsize : (rows n (r+3)).length+1<B) (hcoeff : ∀ a≤n,∀ b≤r+2,a.choose b<B) :
    Spec B (fun σ => σ.inp=[n,r] ∧ (n+1)*(r+3)≤(σ.arrs "choose.table").length ∧
      n≤(σ.arrs "subset.bits").length ∧ (rows n (r+3)).length≤(σ.arrs "catalog.mask").length) fullCommand
      (fun σ τ => τ.out=σ.out++Lax263307.NativeCatalog.words n r) (totalCost n r) := by
  rintro σ ⟨hinp,htable,hbits,hcatalog⟩
  obtain ⟨ν,r1,p1⟩ := read_input_spec B n r (by omega) σ hinp
  obtain ⟨μ,r2,p2⟩ := command_spec B n (r+2) (by omega) hm hsize hcoeff ν
    ⟨p1.1,p1.2,by rwa [Lax455465Proofs.RamFrames.run_array_length r1],
      by rwa [Lax455465Proofs.RamFrames.run_array_length r1],
      by rwa [Lax455465Proofs.RamFrames.run_array_length r1]⟩
  obtain ⟨τ,r3,p3⟩ := emit_spec B n (r+2) (by omega) (by change (rows n (r+3)).length<B; omega) hm μ p2.2
  have hout : μ.out=σ.out := (r1.seq r2).out_eq (by decide)
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by simp only [show r+2+1=r+3 from rfl]; dsimp [totalCost]; omega),?_⟩
  simpa only [hout,show r+2+1=r+3 from rfl,rows_words] using p3

open Lax109476Proofs

def layout := RamAutomaticLayout.layout fullCommand
def program : Lax808846.Ram.Program := Lax808846Proofs.Compile.compileProgram layout fullCommand

theorem compiled_runs_to (n r v width : ℕ) (hv : 0<v)
    (hwidth : v+RamTransfer.layoutAllowance layout≤width)
    (hB : (n+1)*(r+3)+n+r+5<2^v) (hm : 2^n<2^v)
    (hsize : (rows n (r+3)).length+1<2^v) :
    ∃ t≤10*totalCost n r+1,Lax808846.Ram.RunsTo width program [n,r] (Lax263307.NativeCatalog.words n r) t := by
  let room := (n+1)*(r+3)+n+(rows n (r+3)).length+1
  have hcoeff : ∀ a≤n,∀ b≤r+2,a.choose b<2^v := by
    intro a ha b hb
    exact (coefficient_bound n (r+2) a b ha hb).trans_lt (by change (rows n (r+3)).length<2^v; omega)
  obtain ⟨τ,hr,hout⟩ := full_command_spec (2^v) n r hB hm hsize hcoeff
    (initEnv (fun _ => room) [n,r])
    ⟨rfl,by simp [initEnv,room]; omega,by simp [initEnv,room]; omega,by simp [initEnv,room]; omega⟩
  have hinput : ∀ z∈[n,r],z<2^v := by intro z hz; simp only [List.mem_cons,List.not_mem_nil,or_false] at hz; rcases hz with rfl|rfl <;> omega
  obtain ⟨K,hK,hbs⟩ := hr
  obtain ⟨t,ht,hrun⟩ := Lax808846Proofs.Simulation.compileProgram_runsTo
    (RamTransfer.layout_fits hv hwidth) (RamAutomaticLayout.layout_ok fullCommand) hinput hbs
  refine ⟨t,ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 10 hK) 1),?_⟩
  simpa only [program,layout,hout,initEnv,List.nil_append] using hrun

/--
---
conclusion: Lax263307.NativeCatalog.exists_program
---
The native Pascal, subset-decoding and mask-packing loops append exactly
the catalog entries. Physical input/output and compilation preserve this
order. Both executed instructions and sufficient word width are bounded
by one fixed cubic polynomial in n, r and the number of catalog entries.
-/
theorem exists_program : ∃ p : Lax808846.Ram.Program, ∃ c : ℕ, 0<c ∧
    ∀ n r : ℕ, ∀ width : ℕ, c*(n+r+(Lax263307.NativeCatalog.words n r).length+2)^3≤width →
      ∃ t≤c*(n+r+(Lax263307.NativeCatalog.words n r).length+2)^3,
        Lax808846.Ram.RunsTo width p [n,r] (Lax263307.NativeCatalog.words n r) t := by
  let C := 10000+RamTransfer.layoutAllowance layout
  refine ⟨program,C,by dsimp [C]; omega,?_⟩
  intro n r width hwidth
  let N := (rows n (r+3)).length
  let X := n+r+N+2
  let v := 5*X^2+10
  have hN : 1≤N := rows_positive n (r+2)
  have hX : 1≤X := by dsimp [X]; omega
  have hnX : n≤X := by dsimp [X]; omega
  have hn1X : n+1≤X := by dsimp [X]; omega
  have hrX : r≤X := by dsimp [X]; omega
  have hr3X : r+3≤X := by dsimp [X]; omega
  have hNX : N≤X := by dsimp [X]; omega
  have hXX : X≤X^2 := le_self_pow hX (by omega)
  have h23 : X^2≤X^3 := Nat.pow_le_pow_right hX (by omega)
  have h13 : 1≤X^3 := Nat.one_le_pow _ _ (by omega)
  have hdim : (n+1)*(r+3)≤X^2 := by simpa only [pow_two] using Nat.mul_le_mul hn1X hr3X
  have hv : 0<v := by dsimp [v]; omega
  have hguardv : (n+1)*(r+3)+n+r+5<v := by dsimp only [v]; nlinarith only [hdim,hnX,hrX,hXX]
  have hnv : n<v := by omega
  have hsizev : N+1<v := by dsimp only [v]; nlinarith only [hNX,hXX]
  have hvbound : v≤15*X^3 := by dsimp only [v]; omega
  have hw : v+RamTransfer.layoutAllowance layout≤width := by
    have hw' : C*X^3≤width := by simpa only [X,N,rows_words] using hwidth
    have ha := Nat.mul_le_mul_left (RamTransfer.layoutAllowance layout) h13
    dsimp only [C] at hw'
    nlinarith only [hw',hvbound,ha]
  obtain ⟨t,ht,hrun⟩ := compiled_runs_to n r v width hv hw (hguardv.trans Nat.lt_two_pow_self)
    (Nat.pow_lt_pow_right (by omega) hnv) (hsizev.trans Nat.lt_two_pow_self)
  refine ⟨t,ht.trans ?_,hrun⟩
  have h69 : 69*n+33≤102*X := by omega
  have hmul : (69*n+33)*N≤102*X^2 := by
    have hh := Nat.mul_le_mul h69 hNX
    nlinarith only [hh]
  have hpoly : 54*(n+1)*(r+3)+(69*n+33)*N+41≤197*X^2 := by
    have h1 : 1≤X^2 := Nat.one_le_pow _ _ (by omega)
    nlinarith only [hdim,hmul,h1]
  have hmain : (54*(n+1)*(r+3)+(69*n+33)*N+41)*(r+3)≤197*X^3 := by
    have hh := Nat.mul_le_mul hpoly hr3X
    nlinarith only [hh]
  have hrest : 13*N+22≤35*X^3 := by omega
  have hcost : 10*totalCost n r+1≤10000*X^3 := by
    change 10*((54*(n+1)*(r+3)+(69*n+33)*N+41)*(r+3)+13*N+22)+1≤10000*X^3
    nlinarith only [hmain,hrest,h13]
  calc
    10*totalCost n r+1 ≤ 10000*X^3 := hcost
    _ ≤ C*X^3 := Nat.mul_le_mul_right _ (by dsimp [C]; omega)
    _ = C*(n+r+(Lax263307.NativeCatalog.words n r).length+2)^3 := by rw [←rows_words]

end Lax263307Proofs.NativeCatalog
