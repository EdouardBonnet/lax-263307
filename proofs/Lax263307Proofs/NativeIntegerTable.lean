import Lax263307Proofs.NativeRationalTabulate

namespace Lax263307Proofs.NativeIntegerTable

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

def command (count : Expr) (read : Com) : Com := .seq (.assign "fill.length" count)
  (.seq (.assign "lp.length" (.lit 0)) (NativeRationalTabulate.command read))

/-- Materialize integer-valued rational coordinates using a computed
entry count and the existing canonical signed encoding writer. -/
theorem command_spec (B n K : ℕ) (xs : List ℚ) (count : Expr) (read : Com)
    (hB : 3*xs.length+2<B)
    (hcount : ∀ σ,σ.vars "vec.n"=n → count.evalB B σ=some xs.length)
    (hri : "fill.i"∉read.wvars) (hrl : "fill.length"∉read.wvars)
    (hrlen : "lp.length"∉read.wvars) (hra : "lp.input"∉read.warrs)
    (hread : ∀ i (hi : i<xs.length), Spec B (fun σ => σ.vars "vec.n"=n ∧ σ.vars "fill.i"=i) read
      (fun _ τ => τ.vars "vec.n"=n ∧ τ.vars "coefficient.positive"<B ∧ τ.vars "coefficient.negative"<B ∧
        ((τ.vars "coefficient.positive" : ℕ) : ℚ)-τ.vars "coefficient.negative"=xs[i]) K) :
    Spec B (fun σ => σ.vars "vec.n"=n ∧ 3*xs.length≤(σ.arrs "lp.input").length) (command count read)
      (fun _ τ => τ.vars "vec.n"=n ∧ Prefix (NativeRationalTabulate.words xs) "lp.input" τ ∧
        τ.vars "lp.length"=3*xs.length) ((K+39)*xs.length+count.size+9) := by
  have ht := NativeRationalTabulate.command_spec B xs [] (fun σ => σ.vars "vec.n"=n) read K
    (by simpa only [List.length_nil,Nat.zero_add] using hB) hri hrl hrlen hra
    (by intro σ h; simpa using h)
    (fun _ _ rr h => (rr.frame_var "vec.n" (by decide)).trans h)
    (fun _ _ rr h => (rr.frame_var "vec.n" (by decide)).trans h)
    hread
  rintro σ ⟨hn,hroom⟩
  let ν := σ.setVar "fill.length" xs.length
  have r1 : Run B (.assign "fill.length" count) σ ν (count.size+1) := (Run.assign (hcount σ hn)).mono (by omega)
  let μ := ν.setVar "lp.length" 0
  have r2 : Run B (.assign "lp.length" (.lit 0)) ν μ 2 := Run.assign (evalB_lit (show 0<B by omega))
  have hn2 := ((r1.seq r2).frame_var "vec.n" (by simp [Com.wvars])).trans hn
  obtain ⟨τ,r3,p3⟩ := ht μ ⟨hn2,by simp [μ,ν],by simp [μ],
    by simpa only [List.length_nil,Nat.zero_add,RamFrames.run_array_length (r1.seq r2)] using hroom,
    by simp [Prefix]⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),p3.1,
    by simpa only [List.nil_append] using p3.2.2,
    by simpa only [List.length_nil,Nat.zero_add] using p3.2.1⟩

end Lax263307Proofs.NativeIntegerTable
