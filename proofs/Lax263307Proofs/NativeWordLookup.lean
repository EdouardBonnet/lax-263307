import Lax263307Proofs.NativeRationalRead

set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeWordLookup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs

def Context (array : String) {N : ℕ} (keys : Fin N → ℕ) (i : Fin N) (σ : Env) : Prop :=
  Prefix (List.ofFn keys) array σ ∧ σ.vars "lookup.count"=N ∧ σ.vars "lookup.key"=keys i

def Invariant (array : String) {N : ℕ} (keys : Fin N → ℕ) (i : Fin N) (σ : Env) : Prop :=
  Context array keys i σ ∧ σ.vars "lookup.j"≤N ∧
    σ.vars "lookup.result"=if i.val<σ.vars "lookup.j" then i.val else N

def read (array : String) : Com :=
  .assign "lookup.current" (.get array (.var "lookup.j"))

def update : Com := .seq
  (.ite (.eq (.var "lookup.current") (.var "lookup.key"))
    (.assign "lookup.result" (.var "lookup.j")) .skip)
  (.assign "lookup.j" (.add (.var "lookup.j") (.lit 1)))

def step (array : String) : Com := .seq (read array) update

def command (array : String) : Com := .seq (.assign "lookup.result" (.var "lookup.count"))
  (.seq (.assign "lookup.j" (.lit 0))
    (.while (.lt (.var "lookup.j") (.var "lookup.count")) (step array)))

theorem update_spec (B N : ℕ) (keys : Fin N → ℕ) (hinj : Function.Injective keys)
    (hk : ∀ i,keys i<B) (hN : N+2<B) (i j : Fin N) :
    Spec B (fun σ => σ.vars "lookup.j"=j.val ∧ σ.vars "lookup.key"=keys i ∧
      σ.vars "lookup.current"=keys j ∧
      σ.vars "lookup.result"=if i.val<j.val then i.val else N) update
      (fun _ τ => τ.vars "lookup.j"=j.val+1 ∧
        τ.vars "lookup.result"=if i.val<j.val+1 then i.val else N) 10 := by
  have he : keys j=keys i ↔ j=i := ⟨fun h => hinj h,fun h => congrArg keys h⟩
  have hi := i.isLt
  have hj := j.isLt
  have hki := hk i
  have hkj := hk j
  run_vcg
  all_goals simp_all [Fin.ext_iff]
  all_goals simp_all only [Fin.lt_def,Fin.le_def]
  all_goals first | omega | (split_ifs at * <;> omega)

/-- Scan the stored injective keys and return the actual array index of
the requested key. No word value is used as an exponentially large
address; the command scans exactly the allocated catalog entries. -/
theorem command_spec (B N : ℕ) (array : String) (keys : Fin N → ℕ)
    (hinj : Function.Injective keys) (hk : ∀ i,keys i<B) (hN : N+2<B) (i : Fin N) :
    Spec B (Context array keys i) (command array)
      (fun _ τ => Context array keys i τ ∧ τ.vars "lookup.result"=i.val) (17*N+8) := by
  have hbody : Spec B (fun σ => Invariant array keys i σ ∧ σ.vars "lookup.j"<N) (step array)
      (fun σ τ => Invariant array keys i τ ∧ τ.vars "lookup.j"=σ.vars "lookup.j"+1) 13 := by
    rintro σ ⟨⟨hc,hj,hr⟩,hlt⟩
    let j : Fin N := ⟨σ.vars "lookup.j",hlt⟩
    have hg : (σ.arrs array)[j.val]?=some (keys j) := by
      have hh := hc.1 j.val (by simpa using j.isLt)
      simpa only [List.getElem_ofFn] using hh
    let ν := σ.setVar "lookup.current" (keys j)
    have r1 : Run B (read array) σ ν 3 := Run.assign
      (evalB_get (by rw [evalB_var_iff]; exact ⟨rfl,by omega⟩) hg (hk j))
    obtain ⟨τ,r2,p2⟩ := update_spec B N keys hinj hk hN i j ν
      ⟨r1.frame_var "lookup.j" (by simp [read,Com.wvars]),
        (r1.frame_var "lookup.key" (by simp [read,Com.wvars])).trans hc.2.2,
        by simp [ν],(r1.frame_var "lookup.result" (by simp [read,Com.wvars])).trans hr⟩
    have rr := r1.seq r2
    refine ⟨τ,rr,⟨?_,by rw [p2.1]; exact j.isLt,?_⟩,p2.1⟩
    · simpa only [Context,Prefix,rr.frame_arr array (by simp [read,update,Com.warrs]),
        rr.frame_var "lookup.count" (by simp [read,update,Com.wvars]),
        rr.frame_var "lookup.key" (by simp [read,update,Com.wvars])] using hc
    · simpa only [p2.1] using p2.2
  have hloop := Spec.forRangeZero "lookup.j" "lookup.count" (Invariant array keys i) N 13
    (by omega) (fun _ h => h.2.1) (fun _ h => h.1.2.1) hbody
  intro σ hc
  let ν := σ.setVar "lookup.result" N
  have r1 : Run B (.assign "lookup.result" (.var "lookup.count")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hc.2.1.symm,hc.2.1 ▸ (by omega : N<B)⟩)
  have hinit : Invariant array keys i (ν.setVar "lookup.j" 0) := by
    refine ⟨?_,by simp,?_⟩
    · simpa only [ν,Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hc
    · simp [ν]
  obtain ⟨τ,r2,p2⟩ := hloop ν hinit
  refine ⟨τ,(r1.seq r2).mono (by omega),p2.1.1,?_⟩
  simpa only [p2.2,if_pos i.isLt] using p2.1.2.2

end Lax263307Proofs.NativeWordLookup
