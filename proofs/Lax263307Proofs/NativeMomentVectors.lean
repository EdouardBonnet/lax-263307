import Lax263307Proofs.NativeMomentFamily

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP NativeMomentFamily NativeMomentProduce

def entries (N zeros : ℕ) : List ℚ := [1,-1]++List.replicate N 1++List.replicate zeros 0

def value (N q : ℕ) : ℚ := if q=1 then -1 else if q < N+2 then 1 else 0

theorem entries_length (N zeros : ℕ) : (entries N zeros).length=2+N+zeros := by simp [entries]; omega

theorem entries_get (N zeros q : ℕ) (hq : q < 2+N+zeros) :
    (entries N zeros)[q]?=some (value N q) := by
  cases q with
  | zero => simp [entries,value]
  | succ q =>
    cases q with
    | zero => simp [entries,value]
    | succ q =>
      have he : (entries N zeros)[q+2]?=(List.replicate N (1 : ℚ)++List.replicate zeros 0)[q]? := by simp [entries]
      rw [he]
      by_cases h : q < N
      · rw [List.getElem?_append_left (by simpa using h)]
        simp [h,value,show q+2 < N+2 by omega]
      · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt h)]
        have htail : q-N < zeros := by omega
        simp [htail,value,show ¬q+2 < N+2 by omega]

def read : Com := .seq
  (.ite (.eq (.var "fill.i") (.lit 1)) (.assign "coefficient.positive" (.lit 0))
    (.ite (.lt (.var "fill.i") (.add (.var "catalog.count") (.lit 2)))
      (.assign "coefficient.positive" (.lit 1)) (.assign "coefficient.positive" (.lit 0))))
  (.ite (.eq (.var "fill.i") (.lit 1)) (.assign "coefficient.negative" (.lit 1)) (.assign "coefficient.negative" (.lit 0)))

theorem read_spec (B N q : ℕ) (hB : q+N+4 < B) :
    Spec B (fun σ => σ.vars "fill.i"=q ∧ σ.vars "catalog.count"=N) read
      (fun _ τ => Value B (value N q) τ) 18 := by
  by_cases hq : q=1
  · subst q
    run_vcg
    all_goals simp_all [Value,value,Env.setVar]
    all_goals omega
  · by_cases ht : q < N+2
    · run_vcg
      all_goals simp_all [Value,value,Env.setVar]
      all_goals omega
    · run_vcg
      all_goals simp_all [Value,value,Env.setVar]
      all_goals omega

def size (n r : ℕ) : ℕ := 2+dimension n r+dimension n r*(n+4)

def countExpr : Expr := .add (.lit 2) (.mul (.var "catalog.count") (.add (.var "graph.n") (.lit 5)))

def command : Com := .seq (.assign "fill.length" countExpr) (NativeRationalTabulate.command read)

theorem count_spec (B n N : ℕ) (hB : 2+N+N*(n+4)+n+10 < B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "catalog.count"=N)
      (.assign "fill.length" countExpr) (fun _ τ => τ.vars "fill.length"=2+N+N*(n+4)) 8 := by
  have hm : N*(n+5)=N+N*(n+4) := by ring
  simp only [countExpr]
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem vector_entries {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    List.ofFn (MomentLP.program G k r).b++List.ofFn (MomentLP.program G k r).c=
      entries (dimension n r) (dimension n r*(n+4)) := by
  simp only [MomentLP.program,NativeMomentAssembly.ofFn_addCases,List.ofFn_const]
  norm_num only [List.ofFn_succ,List.ofFn_zero,Fin.isValue,Fin.succ_ne_zero,if_true,if_false]
  simp only [entries,List.append_assoc]
  have hz : dimension n r+(dimension n r*n+(dimension n r+dimension n r))+dimension n r=dimension n r*(n+4) := by ring
  rw [←List.replicate_add,hz]

theorem words_exact {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    NativeRationalTabulate.words (entries (dimension n r) (dimension n r*(n+4)))=
      Lax109476.RationalEncoding.encodeVector (MomentLP.program G k r).b++Lax109476.RationalEncoding.encodeVector (MomentLP.program G k r).c := by
  rw [←vector_entries G k r,NativeRationalTabulate.words_append]
  rfl

theorem command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (front : List ℕ)
    (hB : front.length+3*size n r+n+k+r+dimension n r+10 < B) :
    Spec B (fun σ => Data G k r σ ∧ σ.vars "lp.length"=front.length ∧
      front.length+3*size n r ≤ (σ.arrs "lp.input").length ∧ Prefix front "lp.input" σ)
      command (fun _ τ => Data G k r τ ∧ τ.vars "lp.length"=front.length+3*size n r ∧
        Prefix (front++(Lax109476.RationalEncoding.encodeVector (MomentLP.program G k r).b++
          Lax109476.RationalEncoding.encodeVector (MomentLP.program G k r).c)) "lp.input" τ)
      (57*size n r+14) := by
  have hlen : (entries (dimension n r) (dimension n r*(n+4))).length=size n r := entries_length _ _
  have ht := NativeRationalTabulate.command_spec B (entries (dimension n r) (dimension n r*(n+4))) front (Data G k r) read 18
    (by rw [hlen]; omega) (by decide) (by decide) (by decide) (by decide)
    (by intro σ h; simpa [Data,NativeMomentAccess.Data,NativeCatalogMetadata.Data,Prefix] using h)
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
      have hq' : q < size n r := by rwa [hlen] at hq
      obtain ⟨τ,rr,p⟩ := read_spec B (dimension n r) q (by omega) σ ⟨hσ.2,hσ.1.1.1.2.1⟩
      have he := entries_get (dimension n r) (dimension n r*(n+4)) q hq'
      rw [List.getElem?_eq_getElem hq] at he
      refine ⟨τ,rr,data_frame G k r rr
        (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
        (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) hσ.1,?_⟩
      simpa only [Value,Option.some.inj he] using p)
  rintro σ ⟨hd,hl,hr,hp⟩
  obtain ⟨ν,r1,p1⟩ := count_spec B n (dimension n r) (by dsimp [size] at hB; omega) σ ⟨hd.1.1.1,hd.1.1.2.1⟩
  have d1 := data_frame G k r r1
    (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) hd
  obtain ⟨τ,r2,p2⟩ := ht ν ⟨d1,by rw [hlen]; exact p1,
    (r1.frame_var "lp.length" (by decide)).trans hl,
    by rw [hlen,Lax455465Proofs.RamFrames.run_array_length r1]; exact hr,
    by simpa only [Prefix,r1.frame_arr "lp.input" (by decide)] using hp⟩
  refine ⟨τ,(r1.seq r2).mono (by rw [hlen]; omega),p2.1,by simpa only [hlen] using p2.2.1,?_⟩
  simpa only [words_exact G k r] using p2.2.2

end Lax263307Proofs.NativeMomentVectors
