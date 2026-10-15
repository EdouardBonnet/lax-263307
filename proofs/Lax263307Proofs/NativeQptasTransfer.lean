import Lax62Proofs.Refine.Codegen.Cash
import Lax455465Proofs.RamAutomaticLayout
import Lax263307.QPTAS

namespace Lax263307Proofs.NativeQptasTransfer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax455465Proofs
open Lax263307 QPTAS QPTASRuntime WeightedIndependentSet GraphClasses

/-- The registered refinement framework supplies the final descent to
one fixed RAM program. The algorithm supplies only its structured-command
specification and explicit value/time bounds, all independent of word width. -/
theorem qptas_of_spec (C : GraphClass) (command : Com) (c d : ℕ) (hc : 0<c) (hd : 0<d)
    (width cost : ∀ n : ℕ,(Fin n → ℚ) → ℚ → ℕ)
    (hinput : ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],G ∈ C n →
      ∀ weights ε,0<ε → ε<1 → ∀ v∈encodeInput G weights ε,v<2^width n weights ε)
    (hwidth : ∀ n (weights : Fin n → ℚ) ε,0<ε → ε<1 →
      0<width n weights ε ∧ width n weights ε+RamTransfer.layoutAllowance (RamAutomaticLayout.layout command)≤
        timeBound c d n (rationalBitSize weights ε) ε)
    (htime : ∀ n (weights : Fin n → ℚ) ε,0<ε → ε<1 →
      10*cost n weights ε+1≤timeBound c d n (rationalBitSize weights ε) ε)
    (hspec : ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],G ∈ C n →
      ∀ weights ε,0<ε → ε<1 → ∃ (I : Finset (Fin n)) (ext : String → ℕ),
        IsApproximation G weights ε I ∧
        Spec (2^width n weights ε) (fun σ => σ=initEnv ext (encodeInput G weights ε)) command
          (fun _ τ => τ.out=encodeOutput I) (cost n weights ε)) : HasQPTAS C := by
  let L := RamAutomaticLayout.layout command
  refine ⟨compileProgram L command,c,d,hc,hd,?_⟩
  intro n G _ hG weights ε hε hε1
  dsimp only
  intro w hw
  obtain ⟨I,ext,happrox,hs⟩ := hspec n G hG weights ε hε hε1
  let input := encodeInput G weights ε
  have hsolve : Lax808846Proofs.Transfer.Solves L command {input} (fun _ => encodeOutput I)
      (fun _ => 2^width n weights ε) (fun _ => cost n weights ε) := by
    apply Lax62Proofs.Refine.Codegen.solves_of_spec (RamAutomaticLayout.layout_ok command)
    · intro x hx v hv
      have hx' : x=input := Set.mem_singleton_iff.mp hx
      subst x
      exact hinput n G hG weights ε hε hε1 v hv
    · intro x hx
      have hx' : x=input := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨ext,hs⟩
  have hfit : L.FitsWords (2^width n weights ε) w :=
    RamTransfer.layout_fits (hwidth n weights ε hε hε1).1
      ((hwidth n weights ε hε hε1).2.trans hw)
  obtain ⟨t,ht,hr⟩ := hsolve.computesInTime (fun _ _ => hfit) input (Set.mem_singleton input)
  refine ⟨I,happrox,t,?_,hr⟩
  have ht' : t≤10*cost n weights ε+1 := by simpa only [Layout.const] using ht
  exact ht'.trans (htime n weights ε hε hε1)

end Lax263307Proofs.NativeQptasTransfer
