import Lax263307Proofs.NativeMaskUnpack
import Lax263307Proofs.NativeEmptyOutput
import Lax455465Proofs.RamFrames

namespace Lax263307Proofs.NativeImageOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet NativeMasks

def prefixImage {n N : ℕ} (owner : Fin N → Fin n) (I : Finset (Fin N)) (i : ℕ) : Finset (Fin n) :=
  (initialSet I i).image owner

theorem prefixImage_step {n N : ℕ} (owner : Fin N → Fin n) (I : Finset (Fin N)) (i : ℕ) (hi : i<N) :
    prefixImage owner I (i+1)=if (⟨i,hi⟩ : Fin N)∈I then insert (owner ⟨i,hi⟩) (prefixImage owner I i) else prefixImage owner I i := by
  unfold prefixImage
  rw [prefix_succ I i hi]
  split_ifs <;> simp

theorem prefix_insert {n : ℕ} (I : Finset (Fin n)) (v : Fin n) (σ : Env)
    (hp : Prefix (encodeOutput I) "image.output" σ) (hn : n≤(σ.arrs "image.output").length) :
    Prefix (encodeOutput (insert v I)) "image.output" (σ.setArr "image.output" v.val 1) := by
  intro j hj
  have hjn : j<n := by simpa [encodeOutput] using hj
  have hval : v.val<(σ.arrs "image.output").length := v.isLt.trans_le hn
  simp only [arrs_setArr,if_true]
  by_cases he : v.val=j
  · subst j
    rw [List.getElem?_set_self hval]
    simp [encodeOutput]
  · rw [List.getElem?_set_ne he]
    have hvj : (⟨j,hjn⟩ : Fin n)≠v := by intro hh; exact he (congrArg Fin.val hh).symm
    simpa [encodeOutput,hvj] using hp j (by simpa [encodeOutput] using hjn)

structure Context {n N : ℕ} (owner : Fin N → Fin n) (I : Finset (Fin N)) (σ : Env) : Prop where
  order : σ.vars "image.n"=n
  count : σ.vars "image.count"=N
  mask : σ.vars "image.mask"=NativeMasks.mask I
  labels : Prefix (List.ofFn (fun i => (owner i).val)) "image.labels" σ
  room : (σ.arrs "image.output").length=n

def Invariant {n N : ℕ} (owner : Fin N → Fin n) (I : Finset (Fin N)) (σ : Env) : Prop :=
  Context owner I σ ∧ σ.vars "image.i"≤N ∧ Prefix (encodeOutput (prefixImage owner I (σ.vars "image.i"))) "image.output" σ

def read : Com := .seq
  (.assign "image.bit" (.and (.shiftr (.var "image.mask") (.var "image.i")) (.lit 1)))
  (.assign "image.owner" (.get "image.labels" (.var "image.i")))

def branch : Com := .ite (.eq (.var "image.bit") (.lit 1))
  (.store "image.output" (.var "image.owner") (.lit 1)) .skip

def step : Com := .seq read (.seq branch (.assign "image.i" (.add (.var "image.i") (.lit 1))))

theorem context_frame {n N B t : ℕ} {owner : Fin N → Fin n} {I : Finset (Fin N)}
    {c : Com} {σ τ : Env} (rr : Run B c σ τ t) (hc : Context owner I σ)
    (hv : ∀ s∈["image.n","image.count","image.mask"],s∉c.wvars) (hl : "image.labels"∉c.warrs) :
    Context owner I τ := by
  refine ⟨(rr.frame_var _ (hv _ (by simp))).trans hc.order,
    (rr.frame_var _ (hv _ (by simp))).trans hc.count,(rr.frame_var _ (hv _ (by simp))).trans hc.mask,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "image.labels" hl] using hc.labels
  · rw [RamFrames.run_array_length rr]; exact hc.room

private theorem value {B x : ℕ} {name : String} {σ : Env} (hx : σ.vars name=x) (hB : x<B) :
    (Expr.var name).evalB B σ=some x := by
  rw [evalB_var_iff]; exact ⟨hx.symm,hx ▸ hB⟩

theorem step_spec {n N : ℕ} (B : ℕ) (owner : Fin N → Fin n) (I : Finset (Fin N))
    (hB : n+N+5<B) (hm : 2^N<B) :
    Spec B (fun σ => Invariant owner I σ ∧ σ.vars "image.i"<N) step
      (fun σ τ => Invariant owner I τ ∧ τ.vars "image.i"=σ.vars "image.i"+1) 24 := by
  rintro σ ⟨⟨hc,hle,hprefix⟩,hlt⟩
  let i := σ.vars "image.i"
  let v : Fin N := ⟨i,hlt⟩
  let bit := if v∈I then 1 else 0
  have hiB : i<B := by dsimp [i]; omega
  have hbit : bit≤1 := by dsimp [bit]; split_ifs <;> omega
  have hmask : mask I<B := (mask_bound I).trans hm
  have hdiv : mask I/2^i<B := (Nat.div_le_self _ _).trans_lt hmask
  have he : (Expr.and (.shiftr (.var "image.mask") (.var "image.i")) (.lit 1)).evalB B σ=some bit := by
    have hh := evalB_bin (op:=.and)
      (evalB_bin (op:=.shiftr) (value hc.mask hmask) (evalB_var hiB) hdiv)
      (evalB_lit (show 1<B by omega)) (by
        change Nat.land (mask I/2^i) 1<B
        rw [NativeMaskUnpack.bit_value I v]
        exact hbit.trans_lt (by omega))
    exact hh.trans (congrArg some (NativeMaskUnpack.bit_value I v))
  let ν := σ.setVar "image.bit" bit
  have r1 : Run B (.assign "image.bit" (.and (.shiftr (.var "image.mask") (.var "image.i")) (.lit 1))) σ ν 6 := Run.assign he
  have hip : ν.vars "image.i"=i := by simp [ν,i]
  have hlabels : Prefix (List.ofFn (fun j => (owner j).val)) "image.labels" ν := by simpa [Prefix,ν] using hc.labels
  have hget : (ν.arrs "image.labels")[i]?=some (owner v).val := by
    have hh := hlabels i (by simpa only [List.length_ofFn] using hlt)
    rw [List.getElem_ofFn] at hh
    exact hh
  have howner : (owner v).val<B := (owner v).isLt.trans (by omega)
  let μ := ν.setVar "image.owner" (owner v).val
  have r2 : Run B (.assign "image.owner" (.get "image.labels" (.var "image.i"))) ν μ 3 :=
    Run.assign (evalB_get (value hip hiB) hget howner)
  have rd : Run B read σ μ 9 := r1.seq r2
  have hiμ : μ.vars "image.i"=i := by simp [μ,ν,i]
  have hbμ : μ.vars "image.bit"=bit := by simp [μ,ν]
  have hoμ : μ.vars "image.owner"=(owner v).val := by simp [μ]
  have hpμ : Prefix (encodeOutput (prefixImage owner I i)) "image.output" μ := by simpa only [Prefix,μ,ν,arrs_setVar] using hprefix
  have hnμ : (μ.arrs "image.output").length=n := by simpa only [μ,ν,arrs_setVar] using hc.room
  have htest := evalB_condEq (value hbμ (show bit<B by omega)) (evalB_lit (show 1<B by omega))
  obtain ⟨η,rb,hpη,hiη⟩ : ∃ η,Run B branch μ η 7 ∧
      Prefix (encodeOutput (prefixImage owner I (i+1))) "image.output" η ∧ η.vars "image.i"=i := by
    by_cases hv : v∈I
    · let η := μ.setArr "image.output" (owner v).val 1
      have rs : Run B (.store "image.output" (.var "image.owner") (.lit 1)) μ η 3 :=
        Run.store (value hoμ howner) (evalB_lit (show 1<B by omega)) (by rw [hnμ]; exact (owner v).isLt)
      have hc' : (Cond.eq (.var "image.bit") (.lit 1)).evalB B μ=some true := by simpa [bit,hv] using htest
      have rr : Run B branch μ η 7 := (Run.ite_true (d:=.skip) hc' rs).mono (by simp [Cond.size,Expr.size])
      refine ⟨η,rr,?_,by simpa [η] using hiμ⟩
      rw [prefixImage_step owner I i hlt,if_pos hv]
      exact prefix_insert (prefixImage owner I i) (owner v) μ hpμ hnμ.ge
    · have hc' : (Cond.eq (.var "image.bit") (.lit 1)).evalB B μ=some false := by simpa [bit,hv] using htest
      have rr : Run B branch μ μ 7 := (Run.ite_false (c:=.store "image.output" (.var "image.owner") (.lit 1)) hc' Run.skip).mono
        (by simp [Cond.size,Expr.size])
      exact ⟨μ,rr,by simpa only [prefixImage_step owner I i hlt,show ¬(⟨i,hlt⟩ : Fin N)∈I from hv,if_false] using hpμ,hiμ⟩
  let τ := η.setVar "image.i" (i+1)
  have r3 : Run B (.assign "image.i" (.add (.var "image.i") (.lit 1))) η τ 4 := Run.assign
    (evalB_bin (op:=.add) (value hiη hiB) (evalB_lit (show 1<B by omega)) (by change i+1<B; omega))
  have rr : Run B step σ τ 24 := (rd.seq (rb.seq r3)).mono (by omega)
  refine ⟨τ,rr,⟨?_,by simp [τ]; dsimp [i] at *; omega,?_⟩,by simp [τ,i]⟩
  · apply context_frame rr hc
    · intro name hname
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hname
      rcases hname with rfl|rfl|rfl <;> decide
    · decide
  · simpa [τ,Prefix] using hpη

def clear : Com := .seq (.assign "image.clear.i" (.lit 0))
  (.while (.lt (.var "image.clear.i") (.var "image.n")) (Fill.put "image.output" "image.clear.i" (.lit 0)))

def scan : Com := .seq (.assign "image.i" (.lit 0))
  (.while (.lt (.var "image.i") (.var "image.count")) step)

def command : Com := .seq clear (.seq scan (.seq (.assign "emit.count" (.var "image.n"))
  (RamEmitWords.command "image.output" 1)))

theorem prefixImage_full {n N : ℕ} (owner : Fin N → Fin n) (I : Finset (Fin N)) : prefixImage owner I N=I.image owner := by
  unfold prefixImage
  congr 1
  ext v
  simp [initialSet,v.isLt]

/-- Project a selected finite set through arbitrary stored labels, including
repeated labels, and emit its original-order membership vector. -/
theorem command_spec {n N : ℕ} (B : ℕ) (owner : Fin N → Fin n) (I : Finset (Fin N))
    (hB : n+N+5<B) (hm : 2^N<B) :
    Spec B (Context owner I) command
      (fun σ τ => τ.out=σ.out++encodeOutput (I.image owner)) (24*n+28*N+20) := by
  have hfill := Fill.loop_spec B n "image.output" "image.clear.i" "image.n" (.lit 0) (fun _ => 0)
    (by decide) (by omega) (fun _ _ _ _ => evalB_lit (by omega : 0<B))
  have hloop := Spec.forRangeZero "image.i" "image.count" (Invariant owner I) N 24 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.count) (step_spec B owner I hB hm)
  intro σ hc
  have harray : ∃ g,σ.arrs "image.output"=arrOf n g := by
    refine ⟨fun i => (σ.arrs "image.output").getD i 0,?_⟩
    apply List.ext_getElem
    · simp [arrOf,hc.room]
    · intro i hi hj
      simp only [arrOf,List.getElem_map,List.getElem_range]
      exact List.getElem_eq_getD 0
  obtain ⟨ν,r1,⟨g,hg,hzero⟩,hi⟩ := hfill σ ⟨harray,hc.order⟩
  have hcν : Context owner I ν := by
    apply context_frame r1 hc
    · intro name hname
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hname
      rcases hname with rfl|rfl|rfl <;> decide
    · decide
  have hzeros : ν.arrs "image.output"=List.replicate n 0 := by
    rw [hg]
    apply List.ext_getElem
    · simp [arrOf]
    · intro i hi hj
      simp only [arrOf,List.getElem_map,List.getElem_range,List.getElem_replicate]
      exact hzero i (by simpa [arrOf] using hi)
  have hin : Invariant owner I (ν.setVar "image.i" 0) := by
    refine ⟨⟨?_,?_,?_,?_,?_⟩,by simp,?_⟩
    · simpa using hcν.order
    · simpa using hcν.count
    · simpa using hcν.mask
    · simpa [Prefix] using hcν.labels
    · simpa using hcν.room
    · intro i hii
      have hin : i<n := by simpa [prefixImage,initialSet,encodeOutput] using hii
      simp [prefixImage,initialSet,Prefix,hzeros,encodeOutput,hin]
  obtain ⟨μ,r2,po⟩ := hloop ν hin
  have hprefix : Prefix (encodeOutput (I.image owner)) "image.output" μ := by
    simpa only [po.2,prefixImage_full] using po.1.2.2
  let η := μ.setVar "emit.count" n
  have r3 : Run B (.assign "emit.count" (.var "image.n")) μ η 2 :=
    Run.assign (value po.1.1.order (by omega))
  have hdata : RamEmitWords.Data "image.output" 1 (encodeOutput (I.image owner)) η := by
    simpa only [RamEmitWords.Data,Prefix,Nat.one_mul,η,arrs_setVar] using hprefix
  have hout : η.out=σ.out := by
    exact (r3.out_eq (by decide)).trans ((r2.out_eq (by decide)).trans (r1.out_eq (by decide)))
  obtain ⟨τ,r4,houtτ⟩ := RamEmitWords.command_spec B "image.output" 1 (encodeOutput (I.image owner)) σ.out
    (by omega) (by omega) (by simp [encodeOutput]; omega) (by simp [encodeOutput]; omega)
    (by intro z hz; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz; split_ifs <;> omega) η
    ⟨hdata,by simp [η,encodeOutput],hout⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by simp [Expr.size,encodeOutput]; omega),houtτ⟩

end Lax263307Proofs.NativeImageOutput
