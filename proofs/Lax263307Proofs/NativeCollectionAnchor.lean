import Lax263307Proofs.NativeRoundedTrace

namespace Lax263307Proofs.NativeCollectionAnchor

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeCoreMachine

/-- Only the parent's actual local work is excluded. Child activation is
not excluded: its changes must be undone by the checked stack restoration. -/
def workScalars : List String := excludedScalars++component.wvars++
  (Com.ite (.eq (.var "component.active") (.lit 1)) (go 11) (NativeComponentControl.advance 9)).wvars++
  (Com.seq NativeChildGraph.command (go 12)).wvars++(NativeComponentControl.childReply 9 13).wvars

def workArrays : List String := ["recursion.frames"]++component.warrs++
  (Com.ite (.eq (.var "component.active") (.lit 1)) (go 11) (NativeComponentControl.advance 9)).warrs++
  (Com.seq NativeChildGraph.command (go 12)).warrs++(NativeComponentControl.childReply 9 13).warrs

def Anchor (base σ : Env) : Prop :=
  (∀ s,s∉workScalars → σ.vars s=base.vars s) ∧
    (∀ a,a∉workArrays → σ.arrs a=base.arrs a)

theorem refl (σ : Env) : Anchor σ σ := ⟨fun _ _ => rfl,fun _ _ => rfl⟩

theorem trans {base σ τ : Env} (h : Anchor base σ) (hnext : Anchor σ τ) : Anchor base τ :=
  ⟨fun s hs => (hnext.1 s hs).trans (h.1 s hs),
    fun a ha => (hnext.2 a ha).trans (h.2 a ha)⟩

theorem frame {B K : ℕ} {c : Com} {base σ τ : Env} (rr : Run B c σ τ K)
    (hc : Anchor base σ) (hv : ∀ s∈c.wvars,s∈workScalars)
    (ha : ∀ a∈c.warrs,a∈workArrays) : Anchor base τ := by
  constructor
  · intro s hs
    exact (rr.frame_var s (fun h => hs (hv s h))).trans (hc.1 s hs)
  · intro a ha'
    exact (rr.frame_arr a (fun h => ha' (ha a h))).trans (hc.2 a ha')

/-- Parent restoration recovers every anchored field, even when recursive
children overwrite the parent's rounded state, LP cache and catalog. -/
theorem restored {base saved τ : Env} (hc : Anchor base saved)
    (hv : ∀ s,s∉excludedScalars → τ.vars s=saved.vars s)
    (ha : ∀ a,a≠"recursion.frames" → τ.arrs a=saved.arrs a) : Anchor base τ := by
  constructor
  · intro s hs
    have he : s∉excludedScalars := by
      intro h
      apply hs
      simp [workScalars,h]
    exact (hv s he).trans (hc.1 s hs)
  · intro a ha'
    have he : a≠"recursion.frames" := by
      intro h
      apply ha'
      simp [workArrays,h]
    exact (ha a he).trans (hc.2 a ha')

/-- Collection preserves the exact rounded trajectory at this iteration;
only its eventual cut normal and reply may change. -/
theorem stored_state {n : ℕ} {j : ℕ} {state : RoundedOracleSearch.State n}
    {base σ : Env} (hc : Anchor base σ) (hs : NativeRoundedTrace.StoredState j state base) :
    NativeRoundedTrace.StoredState j state σ := by
  refine ⟨?_,?_,(hc.1 _ (by decide)).trans hs.2.2.1,(hc.1 _ (by decide)).trans hs.2.2.2⟩
  · simpa only [Lax455465Proofs.RamVirtualState.Prefix,hc.2 "round.shape" (by decide)] using hs.1
  · simpa only [Lax455465Proofs.RamVirtualState.Prefix,hc.2 "round.center" (by decide)] using hs.2.1

end Lax263307Proofs.NativeCollectionAnchor
