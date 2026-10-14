import Lax263307Proofs.NativeUniformFlow
import Lax263307Proofs.NativeCutLoop

namespace Lax263307Proofs.NativeSeparatorProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs
open Lax759944.RamPolytime
open Lax263307 ComputedSeparators NativeSignedArithmetic
open NativeSeparatorContext NativeUniformFlow
open scoped NNRat

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com := NativeCutLoop.command (callback p coeff)

def timeBound (n H : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ) (tp : Polynomial ℕ) : ℕ :=
  (21*n+callbackTime n H p coeff tp+62)*n+12

/-- The complete bounded native separator loop realizes the cut list
of the chosen functional flow solver, with a uniform workspace and
resource guard independent of its individual remaining sets. -/
theorem exists_program (f : List ℕ → List ℕ) (hf : RamPolytime f) :
    ∃ (p : Lax808846.Ram.Program) (wp tp op : Polynomial ℕ) (coeff : List ℕ),
    (∀ z : ℕ,RamPolynomial.value coeff z=wp.eval z) ∧
    ∀ (b n load k h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0),
    0<n → 0<load → (∀ v,Bounded (2^h) (x v : ℚ)) →
    let H := NativeLargeResources.heightExponent b n load k h
    ∀ w : ℕ,wordHeight n H p wp tp op≤w →
    let cs := cuts (ComputedSeparators.step f G x b load k) n Finset.univ
    Spec (2^w) (fun σ => Context G x b load k (spaceBound n H tp) σ ∧
      σ.vars "separator.remaining"=NativeMasks.mask (Finset.univ : Finset (Fin n)))
      (command p coeff) (fun _ τ => Context G x b load k (spaceBound n H tp) τ ∧
        τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs) ∧
        τ.vars "separator.value"=NativeMasks.mask (separator cs) ∧ τ.vars "separator.count"=cs.length ∧
        Lax455465Proofs.RamVirtualState.Prefix (NativeCutRecords.words cs) "separator.cuts" τ ∧
        τ.vars "separator.position"=2*cs.length) (timeBound n H p coeff tp) := by
  obtain ⟨p,wp,tp,op,coeff,hcoeff,hcallback⟩ := NativeUniformFlow.exists_callback f hf
  refine ⟨p,wp,tp,op,coeff,hcoeff,?_⟩
  intro b n load k h G _ x hn hl hx
  try dsimp only
  let H := NativeLargeResources.heightExponent b n load k h
  let Q := Context G x b load k (spaceBound n H tp)
  let cut := ComputedSeparators.step f G x b load k
  intro w hwidth
  try dsimp only
  have hh : n+30≤H := by dsimp [H,NativeLargeResources.heightExponent]; omega
  have hw := hwidth
  dsimp only [wordHeight] at hw
  have hB : 3*n+5<2^w := NativeUniformWordGuards.scalar _ w (by
    have hs : 3*n+5≤shape n := by dsimp [shape]; nlinarith only []
    omega)
  have hm : 2^n<2^w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hspec := NativeCutLoop.command_spec (2^w) (callbackTime n H p coeff tp) Q cut Finset.univ (callback p coeff)
    hB hm (fun _ hd => hd.order)
    (by
      intro σ s v hs hd
      apply set_var hd s v
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> decide)
    (fun rr hd => frame rr hd (by decide) (by decide) (by decide))
    (fun rr hd => frame rr hd (by decide) (by decide) (by decide))
    (fun R _ => hcallback b n load k h G x hn hl hx w hwidth R)
    (by
      intro s hs
      simp only [NativeCutLoop.preserved,List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;>
        exact callback_variable p coeff _ (by decide) (by decide) (by decide) (by decide))
    (callback_variable p coeff _ (by decide) (by decide) (by decide) (by decide))
    (callback_array p coeff _ (by decide) (by decide) (by decide) (by decide))
  have hbits : n≤spaceBound n H tp := by dsimp [spaceBound]; omega
  have hcuts : 2*n≤spaceBound n H tp := by
    dsimp [spaceBound,NativeSplitInput.wordLength]
    nlinarith only []
  rintro σ ⟨hd,hr⟩
  exact hspec σ ⟨hd,hr,hbits.trans (hd.room "subset.bits" (by simp [workspace])),
    hcuts.trans (hd.room "separator.cuts" (by simp [workspace]))⟩

end Lax263307Proofs.NativeSeparatorProgram
