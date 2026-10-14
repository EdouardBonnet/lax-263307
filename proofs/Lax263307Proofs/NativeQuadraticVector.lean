import Lax263307Proofs.NativeQuadraticTerms
import Lax455465Proofs.RamVectorEncoding

namespace Lax263307Proofs.NativeQuadraticVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open NativeSignedArithmetic NativeQuadraticTerms

def Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n → ℚ) (σ : Env) : Prop :=
  Context G a σ ∧ σ.vars "quadratic.count"=n*n

theorem frame {B n K : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n → ℚ)
    {c : Com} {σ τ : Env} (rr : Run B c σ τ K) (hd : Data G a σ)
    (h0 : "cut.source"∉c.warrs) (h1 : "search.graph"∉c.warrs)
    (h2 : "projection.n"∉c.wvars) (h3 : "quadratic.count"∉c.wvars) : Data G a τ := by
  simpa only [Data,Context,NativeCutRead.Context,Prefix,rr.frame_arr "cut.source" h0,
    rr.frame_arr "search.graph" h1,rr.frame_var "projection.n" h2,rr.frame_var "quadratic.count" h3] using hd

theorem height (M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n → ℚ)
    (hM : 1≤M) (ha : ∀ j,Bounded M (a j)) (i : Fin (n*n)) : Bounded (M^2) (term G a i) := by
  unfold term
  split_ifs
  · simpa only [pow_two] using NativeSumHeight.multiply M M _ _ (ha _) (ha _)
  · simp only [Bounded,Rat.num_zero,Int.natAbs_zero,Rat.den_zero]
    exact ⟨Nat.zero_le _,by nlinarith⟩

def setup : Com := .seq (.assign "lp.position" (.lit 0))
  (.assign "quadratic.count" (.mul (.var "projection.n") (.var "projection.n")))

def command : Com := .seq setup
  (RamVectorEncoding.command "quadratic.i" "quadratic.count" NativeQuadraticTerms.command)

/-- Encode every adjacency-selected rational product in row-major order. -/
theorem command_spec (B M n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : Fin n → ℚ)
    (hM : 1≤M) (hB : 2*M^2+3<B) (hs : 3*(n*n)+3*n+10<B) (ha : ∀ j,Bounded M (a j)) :
    Spec B (fun σ => Context G a σ ∧ 3*(n*n)<(σ.arrs "lp.word").length) command
      (fun _ τ => Data G a τ ∧ Prefix (NativeRationalTabulate.words (terms G a)) "lp.word" τ ∧
        τ.vars "lp.position"=3*(n*n)) ((36*(M^2).size+172)*(n*n)+12) := by
  have h1 : 1<B := by omega
  have hh := RamVectorEncoding.command_spec B (36*(M^2).size+137) (Data G a)
    "quadratic.i" "quadratic.count" (terms G a) [] NativeQuadraticTerms.command h1
    (by simp [terms]; omega)
    (by intro i hi; simp only [terms,List.getElem_ofFn]; exact (height M n G a hM ha ⟨i,by simpa [terms] using hi⟩).1.trans_lt (by omega))
    (by intro i hi; simp only [terms,List.getElem_ofFn]; exact (height M n G a hM ha ⟨i,by simpa [terms] using hi⟩).2.trans_lt (by omega))
    (fun σ h => by simpa only [terms,List.length_ofFn] using h.2)
    (fun σ k h => by simpa only [Data,Context,NativeCutRead.Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    (by
      intro i hi σ hp
      obtain ⟨τ,rr,ht⟩ := NativeQuadraticTerms.command_spec B M n G a ⟨i,by simpa [terms] using hi⟩ hB (by omega) ha σ ⟨hp.1.1,hp.2⟩
      exact ⟨τ,rr,frame G a rr hp.1 (by decide) (by decide) (by decide) (by decide),
        by simpa only [terms,List.getElem_ofFn] using ht.2⟩)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame G a rr h (by decide) (by decide) (by decide) (by decide)) (by decide)
  have hsetup : Spec B (fun σ => σ.vars "projection.n"=n) setup
      (fun _ τ => τ.vars "lp.position"=0 ∧ τ.vars "quadratic.count"=n*n) 6 := by
    run_vcg
    all_goals simp_all
    all_goals omega
  rintro σ ⟨hc,hr⟩
  obtain ⟨ν,r1,p1⟩ := hsetup σ hc.1.2
  have hdν : Data G a ν := by
    refine ⟨?_,p1.2⟩
    simpa only [Context,NativeCutRead.Context,Prefix,r1.frame_arr "cut.source" (by decide),
      r1.frame_arr "search.graph" (by decide),r1.frame_var "projection.n" (by decide)] using hc
  obtain ⟨τ,r2,p2⟩ := hh ν ⟨hdν,by simp [Prefix],by simpa using p1.1,
    by simp only [terms,List.length_ofFn,List.length_nil,Nat.zero_add,RamFrames.run_array_length r1]; exact hr⟩
  refine ⟨τ,(r1.seq r2).mono (by simp only [terms,List.length_ofFn,Nat.add_assoc,Nat.reduceAdd]; omega),p2.1,?_,?_⟩
  · simpa only [List.nil_append,RamVectorEncoding.encode,NativeRationalTabulate.words] using p2.2.1
  · simpa only [List.length_nil,terms,List.length_ofFn,Nat.zero_add] using p2.2.2

end Lax263307Proofs.NativeQuadraticVector
