import Lax263307Proofs.NativeIntegerEncoding

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeRationalTabulate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding

def words (xs : List ℚ) : List ℕ := xs.flatMap encodeRational

theorem words_length (xs : List ℚ) : (words xs).length=3*xs.length := by
  induction xs with
  | nil => simp [words]
  | cons x xs ih => simp only [words,List.flatMap_cons,List.length_append,encodeRational,List.length_cons,List.length_nil] at ih ⊢; omega

theorem words_append (xs ys : List ℚ) : words (xs++ys)=words xs++words ys := List.flatMap_append

theorem words_take_succ (xs : List ℚ) (i : ℕ) (hi : i<xs.length) :
    words (xs.take (i+1))=words (xs.take i)++encodeRational xs[i] := by
  rw [List.take_succ_eq_append_getElem hi,words_append]
  simp [words]

def advance : Com := .assign "fill.i" (.add (.var "fill.i") (.lit 1))

def body (read : Com) : Com := .seq read (.seq NativeIntegerEncoding.append advance)

def command (read : Com) : Com := .seq (.assign "fill.i" (.lit 0))
  (.while (.lt (.var "fill.i") (.var "fill.length")) (body read))

def Invariant (P : Env → Prop) (xs : List ℚ) (front : List ℕ) (σ : Env) : Prop :=
  P σ ∧ σ.vars "fill.length"=xs.length ∧ σ.vars "fill.i"≤xs.length ∧
  σ.vars "lp.length"=front.length+3*σ.vars "fill.i" ∧
  front.length+3*xs.length≤(σ.arrs "lp.input").length ∧
  Prefix (front++words (xs.take (σ.vars "fill.i"))) "lp.input" σ

/-- Append the exact rational encodings of entries computed by a fixed
native command. The command's natural positive and negative parts must
have the prescribed difference; they are not assumed to be canonical. -/
theorem command_spec (B : ℕ) (xs : List ℚ) (front : List ℕ) (P : Env → Prop) (read : Com) (K : ℕ)
    (hB : front.length+3*xs.length+2<B)
    (hri : "fill.i"∉read.wvars) (hrl : "fill.length"∉read.wvars)
    (hrlen : "lp.length"∉read.wvars) (hra : "lp.input"∉read.warrs)
    (hinit : ∀ σ,P σ → P (σ.setVar "fill.i" 0))
    (hwrite : ∀ σ τ,Run B NativeIntegerEncoding.append σ τ 31 → P σ → P τ)
    (hadvance : ∀ σ τ,Run B advance σ τ 4 → P σ → P τ)
    (hread : ∀ i (hi : i<xs.length),Spec B (fun σ => P σ ∧ σ.vars "fill.i"=i) read
      (fun _ τ => P τ ∧ τ.vars "coefficient.positive"<B ∧ τ.vars "coefficient.negative"<B ∧
        ((τ.vars "coefficient.positive" : ℕ) : ℚ)-τ.vars "coefficient.negative"=xs[i]) K) :
    Spec B (fun σ => P σ ∧ σ.vars "fill.length"=xs.length ∧ σ.vars "lp.length"=front.length ∧
      front.length+3*xs.length≤(σ.arrs "lp.input").length ∧ Prefix front "lp.input" σ)
      (command read) (fun _ τ => P τ ∧ τ.vars "lp.length"=front.length+3*xs.length ∧ Prefix (front++words xs) "lp.input" τ)
      ((K+39)*xs.length+6) := by
  have h1 : 1<B := by omega
  have hbody : Spec B (fun σ => Invariant P xs front σ ∧ σ.vars "fill.i"<xs.length)
      (body read) (fun σ τ => Invariant P xs front τ ∧ τ.vars "fill.i"=σ.vars "fill.i"+1) (K+35) := by
    rintro σ ⟨⟨hP,hlen,hle,hcount,hroom,hprefix⟩,hlt⟩
    let i := σ.vars "fill.i"
    have htake : (xs.take i).length=i := by rw [List.length_take,Nat.min_eq_left hle]
    have hfront : (front++words (xs.take i)).length=front.length+3*i := by rw [List.length_append,words_length,htake]
    obtain ⟨ν,r1,p1⟩ := hread i hlt σ ⟨hP,rfl⟩
    obtain ⟨μ,r2,p2⟩ := NativeIntegerEncoding.append_spec B (ν.vars "coefficient.positive") (ν.vars "coefficient.negative")
      (front++words (xs.take i)) h1 p1.2.1 p1.2.2.1 (by rw [hfront]; omega) ν
      ⟨rfl,rfl,by simpa only [Prefix,r1.frame_arr "lp.input" hra] using hprefix,
        by rw [hfront]; exact (r1.frame_var "lp.length" hrlen).trans hcount,
        by rw [hfront,Lax455465Proofs.RamFrames.run_array_length r1]; omega⟩
    have hPμ := hwrite ν μ r2 p1.1
    have hiμ : μ.vars "fill.i"=i :=
      (r2.frame_var "fill.i" (by decide)).trans (r1.frame_var "fill.i" hri)
    let τ := μ.setVar "fill.i" (i+1)
    have r3 : Run B advance μ τ 4 := Run.assign (evalB_bin (op := .add)
      (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega)⟩) (evalB_lit h1) (by change i+1<B; omega))
    have rr := r1.seq (r2.seq r3)
    have ht : τ.vars "fill.i"=i+1 := by simp [τ]
    refine ⟨τ,rr.mono (by omega),⟨hadvance μ τ r3 hPμ,?_,by rw [ht]; omega,?_,?_,?_⟩,ht⟩
    · exact ((r2.seq r3).frame_var "fill.length" (by decide)).trans ((r1.frame_var "fill.length" hrl).trans hlen)
    · rw [ht]
      have hc := (r3.frame_var "lp.length" (by decide)).trans p2.2
      rw [hfront] at hc
      omega
    · rwa [Lax455465Proofs.RamFrames.run_array_length rr]
    · rw [ht,words_take_succ xs i hlt,←List.append_assoc,←p1.2.2.2]
      simpa only [Prefix,r3.frame_arr "lp.input" (by decide)] using p2.1
  have hloop := Spec.forRangeZero "fill.i" "fill.length" (Invariant P xs front) xs.length (K+35)
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.1) hbody
  rintro σ ⟨hP,hlen,hcount,hroom,hprefix⟩
  have hi : Invariant P xs front (σ.setVar "fill.i" 0) := by
    refine ⟨hinit σ hP,?_,by simp,?_,hroom,?_⟩
    · simpa only [vars_setVar,String.reduceEq,if_false] using hlen
    · simpa only [vars_setVar,String.reduceEq,if_true,if_false,Nat.mul_zero,Nat.add_zero] using hcount
    · simpa only [vars_setVar,if_true,List.take_zero,words,List.flatMap_nil,List.append_nil,Prefix,arrs_setVar] using hprefix
  obtain ⟨τ,rr,p⟩ := hloop σ hi
  refine ⟨τ,rr.mono (by nlinarith),p.1.1,?_,?_⟩
  · simpa only [p.2] using p.1.2.2.2.1
  · simpa only [p.2,List.take_length] using p.1.2.2.2.2.2

end Lax263307Proofs.NativeRationalTabulate
