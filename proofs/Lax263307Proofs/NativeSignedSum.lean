import Lax263307Proofs.NativeSignedAccumulate
import Lax263307Proofs.NativeRationalRead

namespace Lax263307Proofs.NativeSignedSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs Lax455465Proofs.RamRational
open NativeSignedArithmetic

def partialSum (xs : List ℚ) (i : ℕ) : ℚ := (xs.take i).sum

theorem partial_step (xs : List ℚ) (i : ℕ) (hi : i<xs.length) :
    partialSum xs (i+1)=partialSum xs i+xs[i] := by
  simp only [partialSum,List.take_succ_eq_append_getElem hi,List.sum_append,List.sum_singleton]

def Context (xs : List ℚ) (σ : Env) : Prop :=
  Prefix (NativeRationalTabulate.words xs) "sum.input" σ ∧ σ.vars "sum.count"=xs.length

def Invariant (xs : List ℚ) (σ : Env) : Prop :=
  Context xs σ ∧ σ.vars "sum.i"≤xs.length ∧ Stored "sum.value" (partialSum xs (σ.vars "sum.i")) σ

def setup : Com := .seq (.assign "sum.value.s" (.lit 0))
  (.seq (.assign "sum.value.n" (.lit 0)) (.assign "sum.value.d" (.lit 1)))

def read : Com := .seq (.assign "read.cursor" (.mul (.lit 3) (.var "sum.i")))
  (NativeRationalRead.command "sum.input")

def advance : Com := .assign "sum.i" (.add (.var "sum.i") (.lit 1))

def body : Com := .seq read (.seq NativeSignedAccumulate.command advance)

def command : Com := .seq setup
  (.seq (.seq (.assign "sum.i" (.lit 0)) (.while (.lt (.var "sum.i") (.var "sum.count")) body))
    (load "sum.value"))

theorem setup_spec (B : ℕ) (h1 : 1<B) :
    Spec B (fun _ => True) setup (fun _ τ => Stored "sum.value" 0 τ) 6 := by
  run_vcg
  all_goals simp_all [Stored,fractionValue]

theorem read_spec (B H : ℕ) (xs : List ℚ) (i : ℕ) (hi : i<xs.length)
    (hs : 3*xs.length+10<B) (hH : H<B) (hx : ∀ x∈xs,Bounded H x) :
    Spec B (fun σ => Context xs σ ∧ σ.vars "sum.i"=i) read
      (fun _ τ => FractionOutput xs[i] τ) 21 := by
  rintro σ ⟨hc,hiσ⟩
  let ν := σ.setVar "read.cursor" (3*i)
  have r1 : Run B (.assign "read.cursor" (.mul (.lit 3) (.var "sum.i"))) σ ν 4 :=
    Run.assign (evalB_bin (op := .mul) (evalB_lit (by omega : 3<B))
      (by rw [evalB_var_iff]; exact ⟨hiσ.symm,hiσ ▸ (by omega : i<B)⟩)
      (by change 3*i<B; omega))
  have hxi := hx xs[i] (List.getElem_mem hi)
  obtain ⟨τ,r2,p2⟩ := NativeRationalRead.vector_entry_spec B "sum.input" [] [] xs i hi (by omega)
    (by simp; omega) (hxi.1.trans_lt hH) (hxi.2.trans_lt hH) ν
    ⟨by simpa only [List.nil_append,List.append_nil,Prefix,ν,arrs_setVar] using hc.1,by simp [ν]⟩
  exact ⟨τ,r1.seq r2,p2.1⟩

/-- An actual bounded rational accumulation loop, with a height
invariant on every partial sum and a cost linear in the vector length
and the uniform operand bit length. -/
theorem command_spec (B H : ℕ) (xs : List ℚ) (hB : 2*H^2+3<B)
    (hs : 3*xs.length+10<B) (hx : ∀ x∈xs,Bounded H x)
    (hp : ∀ i≤xs.length,Bounded H (partialSum xs i)) :
    Spec B (Context xs) command (fun _ τ => Context xs τ ∧ FractionOutput xs.sum τ)
      ((36*(H^2).size+149)*xs.length+18) := by
  have h1 : 1<B := by nlinarith
  have hH : H<B := by nlinarith
  have hbody : Spec B (fun σ => Invariant xs σ ∧ σ.vars "sum.i"<xs.length) body
      (fun σ τ => Invariant xs τ ∧ τ.vars "sum.i"=σ.vars "sum.i"+1)
      (36*(H^2).size+145) := by
    rintro σ ⟨⟨hc,hle,hacc⟩,hlt⟩
    let i := σ.vars "sum.i"
    obtain ⟨ν,r1,p1⟩ := read_spec B H xs i hlt hs hH hx σ ⟨hc,rfl⟩
    have haccν : Stored "sum.value" (partialSum xs i) ν := by
      simpa only [Stored,String.reduceAppend,r1.frame_var "sum.value.s" (by decide),
        r1.frame_var "sum.value.n" (by decide),r1.frame_var "sum.value.d" (by decide)] using hacc
    obtain ⟨μ,r2,p2⟩ := NativeSignedAccumulate.command_spec B H (partialSum xs i) xs[i] hB
      (hp i hle) (hx xs[i] (List.getElem_mem hlt)) ν ⟨haccν,p1⟩
    have hiμ : μ.vars "sum.i"=i := (r1.seq r2).frame_var "sum.i" (by decide)
    let τ := μ.setVar "sum.i" (i+1)
    have r3 : Run B advance μ τ 4 := Run.assign
      (evalB_bin (op := .add)
        (by rw [evalB_var_iff]; exact ⟨hiμ.symm,hiμ ▸ (by omega : i<B)⟩)
        (evalB_lit h1) (by change i+1<B; omega))
    have ht : τ.vars "sum.i"=i+1 := by simp [τ]
    have rr := r1.seq (r2.seq r3)
    refine ⟨τ,rr.mono (by omega),⟨?_,by rw [ht]; omega,?_⟩,ht⟩
    · simpa only [Context,Prefix,rr.frame_arr "sum.input" (by decide),
        rr.frame_var "sum.count" (by decide)] using hc
    · rw [ht,partial_step xs i hlt]
      simpa only [Stored,String.reduceAppend,r3.frame_var "sum.value.s" (by decide),
        r3.frame_var "sum.value.n" (by decide),r3.frame_var "sum.value.d" (by decide)] using p2.1
  have hloop := Spec.forRangeZero "sum.i" "sum.count" (Invariant xs) xs.length
    (36*(H^2).size+145) (by omega) (fun _ h => h.2.1) (fun _ h => h.1.2) hbody
  intro σ hc
  obtain ⟨ν,r1,p1⟩ := setup_spec B h1 σ trivial
  have hcν : Context xs ν := by
    simpa only [Context,Prefix,r1.frame_arr "sum.input" (by decide),
      r1.frame_var "sum.count" (by decide)] using hc
  have hinit : Invariant xs (ν.setVar "sum.i" 0) := by
    refine ⟨?_,by simp,?_⟩
    · simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hcν
    · simpa only [Stored,String.reduceAppend,vars_setVar,String.reduceEq,if_false,if_true,
        partialSum,List.take_zero,List.sum_nil] using p1
  obtain ⟨μ,r2,p2⟩ := hloop ν hinit
  have hsum : Bounded H xs.sum := by simpa only [partialSum,List.take_length] using hp xs.length le_rfl
  have hstored : Stored "sum.value" xs.sum μ := by
    simpa only [p2.2,partialSum,List.take_length] using p2.1.2.2
  obtain ⟨τ,r3,p3⟩ := load_spec B "sum.value" xs.sum h1
    (hsum.1.trans_lt hH) (hsum.2.trans_lt hH) (by decide) μ hstored
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by simp only [Nat.add_assoc,Nat.reduceAdd]; omega),?_,p3⟩
  simpa only [Context,Prefix,r3.frame_arr "sum.input" (by decide),
    r3.frame_var "sum.count" (by decide)] using p2.1.1

theorem bounded_spec (B M : ℕ) (xs : List ℚ) (hM : 1≤M)
    (hB : 2*((2*M)^(xs.length+1))^2+3<B) (hs : 3*xs.length+10<B)
    (hx : ∀ x∈xs,Bounded M x) :
    Spec B (Context xs) command (fun _ τ => Context xs τ ∧ FractionOutput xs.sum τ)
      ((36*(((2*M)^(xs.length+1))^2).size+149)*xs.length+18) := by
  exact command_spec B ((2*M)^(xs.length+1)) xs hB hs
    (NativeSumHeight.uniform_entry M xs hM hx)
    (fun i _ => NativeSumHeight.uniform_partial M xs hM hx i)

end Lax263307Proofs.NativeSignedSum
