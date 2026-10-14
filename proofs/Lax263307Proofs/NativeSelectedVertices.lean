import Lax263307Proofs.NativeRestrictionOrder

set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeSelectedVertices

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet NativeRestrictionOrder

def Context {n : ℕ} (R : Finset (Fin n)) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ Prefix (encodeOutput R) "subset.bits" σ ∧ n≤(σ.arrs "restrict.vertices").length

def Invariant {n : ℕ} (R : Finset (Fin n)) (σ : Env) : Prop :=
  Context R σ ∧ σ.vars "restrict.i"≤n ∧
    Prefix (selectedPrefix R (σ.vars "restrict.i")) "restrict.vertices" σ ∧
    σ.vars "restrict.count"=(selectedPrefix R (σ.vars "restrict.i")).length

def choose : Com := .ite (.eq (.var "restrict.bit") (.lit 1))
  (RamWordBuffer.append "restrict.vertices" "restrict.count" (.var "restrict.i")) .skip

def step : Com := .seq (.assign "restrict.bit" (.get "subset.bits" (.var "restrict.i")))
  (.seq choose (.assign "restrict.i" (.add (.var "restrict.i") (.lit 1))))

theorem step_spec (B n : ℕ) (R : Finset (Fin n)) (hB : n+2<B) :
    Spec B (fun σ => Invariant R σ ∧ σ.vars "restrict.i"<n) step
      (fun σ τ => Invariant R τ ∧ τ.vars "restrict.i"=σ.vars "restrict.i"+1) 18 := by
  rintro σ ⟨⟨⟨hn,hsource,hroom⟩,hle,hprefix,hcount⟩,hlt⟩
  let i := σ.vars "restrict.i"
  let bit := if (⟨i,hlt⟩ : Fin n)∈R then 1 else 0
  have hbitB : bit<B := by dsimp [bit]; split_ifs <;> omega
  have hilen : i<(encodeOutput R).length := by simpa only [encodeOutput,List.length_ofFn] using hlt
  have hg := hsource i hilen
  have he : (encodeOutput R)[i]=bit := by simp only [encodeOutput,List.getElem_ofFn]; rfl
  rw [he] at hg
  let ν := σ.setVar "restrict.bit" bit
  have r1 : Run B (.assign "restrict.bit" (.get "subset.bits" (.var "restrict.i"))) σ ν 3 :=
    Run.assign (evalB_get (evalB_var (by omega : σ.vars "restrict.i"<B)) hg hbitB)
  have hlen := prefix_length R i
  have htest : (Cond.eq (.var "restrict.bit") (.lit 1)).evalB B ν=some (decide (bit=1)) :=
    evalB_condEq (by rw [evalB_var_iff]; simp [ν,hbitB]) (evalB_lit (by omega))
  have hc : ∃ μ,Run B choose ν μ 11 ∧ Prefix (selectedPrefix R (i+1)) "restrict.vertices" μ ∧
      μ.vars "restrict.count"=(selectedPrefix R (i+1)).length := by
    by_cases hmem : (⟨i,hlt⟩ : Fin n)∈R
    · obtain ⟨μ,rr,pp⟩ := RamWordBuffer.append_spec B "restrict.vertices" "restrict.count" (selectedPrefix R i) i
        (.var "restrict.i") (by omega) (by omega) ν
        ⟨by simpa only [Prefix,ν,arrs_setVar] using hprefix,
          by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hcount,
          by simpa only [ν,arrs_setVar] using (show (selectedPrefix R i).length<(σ.arrs "restrict.vertices").length by omega),
          by rw [evalB_var_iff]; simp only [ν,vars_setVar,String.reduceEq,if_false]; exact ⟨rfl,by omega⟩⟩
      have hh : Run B choose ν μ 11 := (Run.ite_true (d:=.skip) (by simpa [bit,hmem] using htest) rr).mono (by decide)
      exact ⟨μ,hh,by simpa only [prefix_step R i hlt,if_pos hmem] using pp.1,
        by simpa only [prefix_step R i hlt,if_pos hmem,List.length_append,List.length_singleton] using pp.2⟩
    · have hh : Run B choose ν ν 11 :=
        (Run.ite_false (c:=RamWordBuffer.append "restrict.vertices" "restrict.count" (.var "restrict.i"))
          (by simpa [bit,hmem] using htest) Run.skip).mono (by decide)
      exact ⟨ν,hh,by simpa only [prefix_step R i hlt,if_neg hmem,Prefix,ν,arrs_setVar] using hprefix,
        by simpa only [prefix_step R i hlt,if_neg hmem,ν,vars_setVar,String.reduceEq,if_false] using hcount⟩
  obtain ⟨μ,r2,hp2,hc2⟩ := hc
  have hiμ : μ.vars "restrict.i"=i := (r1.seq r2).frame_var "restrict.i" (by decide)
  let τ := μ.setVar "restrict.i" (i+1)
  have r3 : Run B (.assign "restrict.i" (.add (.var "restrict.i") (.lit 1))) μ τ 4 :=
    Run.assign (evalB_bin (op:=.add) (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega : i<B)⟩)
      (evalB_lit (by omega)) (by change i+1<B; omega))
  have rr := r1.seq (r2.seq r3)
  refine ⟨τ,rr,?_,by simp [τ,i]⟩
  refine ⟨⟨(rr.frame_var "graph.n" (by decide)).trans hn,?_,?_⟩,by simp [τ]; omega,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "subset.bits" (by decide)] using hsource
  · rwa [RamFrames.run_array_length rr]
  · simpa only [τ,vars_setVar,if_true,Prefix,arrs_setVar] using hp2
  · simpa only [τ,vars_setVar,String.reduceEq,if_false,if_true] using hc2

def command : Com := .seq (.assign "restrict.count" (.lit 0))
  (.seq (.assign "restrict.i" (.lit 0)) (.while (.lt (.var "restrict.i") (.var "graph.n")) step))

/-- Enumerate an induced vertex set in increasing original-label order,
so that every stored label agrees with ComputedSeparators.label. -/
theorem command_spec (B n : ℕ) (R : Finset (Fin n)) (hB : n+2<B) :
    Spec B (Context R) command
      (fun _ τ => Context R τ ∧ Prefix (words R) "restrict.vertices" τ ∧ τ.vars "restrict.count"=R.card)
      (22*n+8) := by
  have hloop := Spec.forRangeZero "restrict.i" "graph.n" (Invariant R) n 18 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1.1) (step_spec B n R hB)
  intro σ hc
  let ν := σ.setVar "restrict.count" 0
  have r1 : Run B (.assign "restrict.count" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hi : Invariant R (ν.setVar "restrict.i" 0) := by
    refine ⟨?_,by simp,?_,?_⟩
    · simpa only [Context,Prefix,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hc
    · simp [Prefix,prefix_zero]
    · simp [ν,prefix_zero]
  obtain ⟨τ,r2,ht⟩ := hloop ν hi
  refine ⟨τ,(r1.seq r2).mono (by omega),ht.1.1,?_,?_⟩
  · simpa only [ht.2,prefix_full] using ht.1.2.2.1
  · simpa only [ht.2,prefix_full,words,List.length_ofFn] using ht.1.2.2.2

end Lax263307Proofs.NativeSelectedVertices
