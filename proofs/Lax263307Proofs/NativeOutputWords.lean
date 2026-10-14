import Lax263307Proofs.NativeRawOracle

namespace Lax263307Proofs.NativeOutputWords

open Lax455465Proofs Lax455465Proofs.SparseRam
open Lax808846.Ram

def OutputWords (w : ℕ) (s : SparseState) : Prop := ∀ z∈s.out,z<2^w

theorem effect_words (w : ℕ) (i : Instr) (s τ : SparseState)
    (ho : OutputWords w s) (hs : effect w i s=some τ) : OutputWords w τ := by
  cases i <;> simp only [effect] at hs
  all_goals first
    | solve | (cases hs; exact ho)
    | solve | (cases hi : s.inp.head? <;>
        (try simp only [hi,Option.map_some,Option.map_none] at hs) <;> cases hs <;> exact ho)
    | solve |
        cases hs
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact ho z hz
        · have he := List.mem_singleton.mp hz
          rw [he]
          exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem step_words (w : ℕ) (p : Program) (s τ : SparseState)
    (ho : OutputWords w s) (hs : SparseRam.step w p s=some τ) : OutputWords w τ := by
  unfold SparseRam.step at hs
  cases hi : p[s.pc]? with
  | none => simp only [hi,Option.bind_none] at hs; cases hs
  | some i =>
    simp only [hi,Option.bind_some] at hs
    exact effect_words w i s τ ho hs

theorem run_words (w : ℕ) (p : Program) (t : ℕ) (s τ : SparseState)
    (ho : OutputWords w s) (hr : SparseRam.run w p t s=some τ) : OutputWords w τ := by
  induction t generalizing s with
  | zero => simp only [SparseRam.run] at hr; cases hr; exact ho
  | succ t ih =>
    simp only [SparseRam.run] at hr
    cases hs : SparseRam.step w p s with
    | none => simp only [hs,Option.bind_none] at hr; cases hr
    | some μ =>
      simp only [hs,Option.bind_some] at hr
      exact ih μ (step_words w p s μ ho hs) hr

/-- Every actual RAM output word is bounded by that RAM's word length,
independently of the running-time interface used to invoke it. -/
theorem runs_to_words (w : ℕ) (p : Program) (xs ys : List ℕ) (t : ℕ)
    (hr : RunsTo w p xs ys t) : ∀ z∈ys,z<2^w := by
  obtain ⟨k,hkt,s,hs,hhalt,hout,_,_⟩ := SparseRam.exists_execution w p xs ys t hr
  have ho := run_words w p k (init xs) s (by simp [OutputWords,init]) hs
  simpa only [OutputWords,hout] using ho

end Lax263307Proofs.NativeOutputWords
