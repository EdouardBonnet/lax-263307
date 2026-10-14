import Lax263307Proofs.NativeFullSetMask
import Lax263307Proofs.NativeSeparatorProgram
import Lax263307Proofs.NativeCutPieces

namespace Lax263307Proofs.NativeSeparatorOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.RamPolytime
open Lax263307 ComputedSeparators NativeSignedArithmetic
open NativeSeparatorContext NativeUniformFlow
open scoped NNRat

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq NativeFullSetMask.command (.seq (NativeSeparatorProgram.command p coeff) NativeCutPieces.command)

def timeBound (n H : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ) (tp : Polynomial ℕ) : ℕ :=
  14*n+8+NativeSeparatorProgram.timeBound n H p coeff tp+37*(n+1)+10

theorem cuts_length {n : ℕ} (cut : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))
    (fuel : ℕ) (R : Finset (Fin n)) : (cuts cut fuel R).length ≤ fuel := by
  induction fuel generalizing R with
  | zero => simp [cuts]
  | succ fuel ih =>
    simp only [cuts]
    split_ifs
    · simp
    · simpa only [List.length_cons] using Nat.succ_le_succ (ih _)

/-- One fixed source command constructs all component masks, including
initialization of the full vertex set and the chosen flow solver calls. -/
theorem exists_program (f : List ℕ → List ℕ) (hf : RamPolytime f) :
    ∃ (p : Lax808846.Ram.Program) (wp tp op : Polynomial ℕ) (coeff : List ℕ),
    (∀ z : ℕ,RamPolynomial.value coeff z=wp.eval z) ∧
    ∀ (b n load k h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0),
    0<n → 0<load → (∀ v,Bounded (2^h) (x v : ℚ)) →
    let H := NativeLargeResources.heightExponent b n load k h
    ∀ w : ℕ,wordHeight n H p wp tp op≤w →
    let cs := cuts (ComputedSeparators.step f G x b load k) n Finset.univ
    Spec (2^w) (fun σ => Context G x b load k (spaceBound n H tp) σ ∧
      n+1≤(σ.arrs "separator.pieces").length)
      (command p coeff) (fun _ τ => Context G x b load k (spaceBound n H tp) τ ∧
        τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs) ∧
        τ.vars "separator.value"=NativeMasks.mask (separator cs) ∧ τ.vars "separator.count"=cs.length ∧
        Prefix (NativeCutRecords.words cs) "separator.cuts" τ ∧
        τ.vars "separator.position"=2*cs.length ∧
        Prefix (NativeCutPieces.words cs) "separator.pieces" τ)
      (timeBound n H p coeff tp) := by
  obtain ⟨p,wp,tp,op,coeff,hcoeff,hsep⟩ := NativeSeparatorProgram.exists_program f hf
  refine ⟨p,wp,tp,op,coeff,hcoeff,?_⟩
  intro b n load k h G _ x hn hl hx
  try dsimp only
  let H := NativeLargeResources.heightExponent b n load k h
  intro w hwidth
  try dsimp only
  let cs := cuts (ComputedSeparators.step f G x b load k) n Finset.univ
  have hcs : cs.length≤n := cuts_length _ _ _
  have hh : n+30≤H := by dsimp [H,NativeLargeResources.heightExponent]; omega
  have hw := hwidth
  dsimp only [wordHeight] at hw
  have hm : 2^n<2^w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hB : 2*n+5<2^w := NativeUniformWordGuards.scalar _ w (by
    have hs : 2*n+5≤shape n := by dsimp [shape]; nlinarith only []
    omega)
  rintro σ ⟨hd,hr⟩
  obtain ⟨ν,r1,p1⟩ := NativeFullSetMask.command_spec (2^w) n (by omega) hm σ hd.order
  have hd1 := frame r1 hd (by decide) (by decide) (by decide)
  obtain ⟨μ,r2,p2⟩ := hsep b n load k h G x hn hl hx w hwidth ν ⟨hd1,p1⟩
  have hr2 : cs.length+1≤(μ.arrs "separator.pieces").length := by
    rw [RamFrames.run_array_length r2,RamFrames.run_array_length r1]
    omega
  obtain ⟨τ,r3,p3⟩ := NativeCutPieces.command_spec (2^w) cs (by omega) hm μ
    ⟨⟨p2.2.2.2.2.1,p2.2.2.2.1,p2.2.1⟩,hr2⟩
  have hd3 := frame r3 p2.1 (by decide) (by decide) (by decide)
  refine ⟨τ,(r1.seq (r2.seq r3)).mono ?_,hd3,p3.1.remaining,?_,p3.1.count,p3.1.cuts,?_,p3.2⟩
  · dsimp only [timeBound]
    have ht := Nat.mul_le_mul_left 37 (Nat.add_le_add_right hcs 1)
    omega
  · exact (r3.frame_var "separator.value" (by decide)).trans p2.2.2.1
  · exact (r3.frame_var "separator.position" (by decide)).trans p2.2.2.2.2.2

end Lax263307Proofs.NativeSeparatorOutput
