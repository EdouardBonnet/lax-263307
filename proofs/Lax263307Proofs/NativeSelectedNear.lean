import Lax263307Proofs.NativeRecursiveSetup
import Lax263307Proofs.NativeSelectedParts
import Lax263307Proofs.NativeNearResources

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedNear

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses AlgorithmParameters RationalConditioning HeavyRationalConditioning ComputedSeparators
open NativeCoreMachine NativeUniformFlow
open scoped NNRat

structure Program (f : List ℕ → List ℕ) where
  code : Lax808846.Ram.Program
  width : Polynomial ℕ
  time : Polynomial ℕ
  output : Polynomial ℕ
  coeff : List ℕ
  coefficients : ∀ z : ℕ,RamPolynomial.value coeff z=width.eval z
  call : ∀ (b n load k h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0),
    0<n → 0<load → (∀ v,NativeSignedArithmetic.Bounded (2^h) (x v : ℚ)) →
    let H := NativeLargeResources.heightExponent b n load k h
    ∀ w : ℕ,wordHeight n H code width time output≤w →
    let cs := cuts (step f G x b load k) n Finset.univ
    Spec (2^w) (fun σ => NativeSeparatorContext.Context G x b load k (spaceBound n H time) σ ∧
      n+1≤(σ.arrs "separator.pieces").length)
      (NativeSeparatorOutput.command code coeff)
      (fun _ τ => NativeSeparatorContext.Context G x b load k (spaceBound n H time) τ ∧
        τ.vars "separator.remaining"=NativeMasks.mask (remaining Finset.univ cs) ∧
        τ.vars "separator.value"=NativeMasks.mask (separator cs) ∧ τ.vars "separator.count"=cs.length ∧
        Prefix (NativeCutRecords.words cs) "separator.cuts" τ ∧ τ.vars "separator.position"=2*cs.length ∧
        Prefix (NativeCutPieces.words cs) "separator.pieces" τ)
      (NativeSeparatorOutput.timeBound n H code coeff time)

theorem exists_program (f : List ℕ → List ℕ) (hf : Lax759944.RamPolytime.RamPolytime f) :
    Nonempty (Program f) := by
  obtain ⟨p,wp,tp,op,coeff,hcoeff,hcall⟩ := NativeSeparatorOutput.exists_program f hf
  exact ⟨⟨p,wp,tp,op,coeff,hcoeff,hcall⟩⟩

/-- The complete near-branch setup follows from the selected solver,
feasible LP certificate and hereditary child domain. No child execution
or phase-execution premise is present. -/
theorem setup {C : GraphClass} (hereditary : IsHereditary C)
    {flow : List ℕ → List ℕ} (fp : Program flow) (cfg : Config)
    (hcode : fp.code=cfg.flow) (hcoeff : fp.coeff=cfg.flowWidth)
    (hsep : NearOracle.SeparatorCorrect C flow cfg.a cfg.K cfg.b) (hK : 0<cfg.K) (hb : 0<cfg.b)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k fuel S v H T w rootN capacity childSteps childTime : ℕ)
    (extent : String → ℕ) (front : List ℕ)
    (hi : NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length)
      capacity (fuel+1) n G k front.length)
    (hn : 1<n) (hD : 4≤D) (hlarge : cutoff cfg.a cfg.K cfg.b n D<k)
    (x : Fin (MomentLP.dimension n (level cfg.a cfg.K cfg.b n D)) → ℚ)
    (hy : LinearRelaxation.IsFeasible G k (level cfg.a cfg.K cfg.b n D) (realVector (MomentLP.decode x)))
    (hx : ∀ i,NativeSignedArithmetic.Bounded (2^H) (x i))
    (htarget : n+1≤T)
    (bounds : NativeNearExecution.Bounds n (level cfg.a cfg.K cfg.b n D) D k
      (sparsity cfg.a cfg.K cfg.b n D) (2^H) (2*H) T fuel S w cfg extent front)
    (hwidth : wordHeight n (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H))
      fp.code fp.width fp.time fp.output≤w)
    (hspace : ∀ a∈NativeSeparatorContext.workspace,
      spaceBound n (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H)) fp.time≤extent a)
    (child : (A : Finset (Fin n)) → ℕ → Option (Finset (Fin A.card))) :
    NativeRecursiveSetup.Near D k (sparsity cfg.a cfg.K cfg.b n D) cfg.b (load cfg.b n D)
      fuel S v (2^H) (2*H) T w
      (spaceBound n (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H)) fp.time)
      (NativeSeparatorOutput.timeBound n (NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H))
        fp.code fp.coeff fp.time) childSteps childTime cfg G flow x extent front child
      (NativeRecursiveDomain.eligible C rootN (S*(frameArrays cfg).length+(frameScalars cfg).length) capacity) := by
  have hnroot : n≤rootN := hi.2.2.1
  have hload : 0<load cfg.b n D := by unfold load logarithm; positivity
  have decoded : ∀ T,NativeSignedArithmetic.Bounded (2^H) (MomentLP.decode x T) := by
    intro T
    exact hx ((CoordinateCatalog.indexing n _).symm T)
  have parts := NativeSelectedParts.selected hsep hK hb G hi.1 (by omega) D k hD hlarge (MomentLP.decode x) hy
  refine ⟨bounds,hx,fun A hA => (parts A hA).1,?_,hspace,?_,?_⟩
  · intro A hA vertices
    exact (NativeSelectedParts.target_bound D (by omega) _ (parts A hA).2.1 vertices).trans htarget
  · intro A
    dsimp only
    have hcost : ∀ v,NativeSignedArithmetic.Bounded (2^(2*H))
        (NearOracle.costs (MomentLP.decode x) A v : ℚ) := by
      -- Flow calls only occur after a successful bounded conditioning.
      -- The unconditional quotient bound also covers a missing coordinate.
      intro v
      have hnum : NativeSignedArithmetic.Bounded (2^H)
          (rationalValue (MomentLP.decode x) (insert v A)) := by
        unfold rationalValue
        split_ifs
        · exact decoded _
        · exact ⟨by simp,by simp; exact Nat.one_le_two_pow⟩
      have hden : NativeSignedArithmetic.Bounded (2^H) (rationalValue (MomentLP.decode x) A) := by
        unfold rationalValue
        split_ifs
        · exact decoded _
        · exact ⟨by simp,by simp; exact Nat.one_le_two_pow⟩
      have h := NativePositiveQuotient.height (2^H) _ _ Nat.one_le_two_pow hnum hden
      change NativeSignedArithmetic.Bounded (2^(2*H))
        (max 0 (rationalValue (MomentLP.decode x) (insert v A) / rationalValue (MomentLP.decode x) A))
      simpa only [←pow_mul,Nat.mul_comm H 2] using h
    simpa only [hcode,hcoeff] using fp.call cfg.b n (load cfg.b n D) k (2*H) G
      (NearOracle.costs (MomentLP.decode x) A) (by omega) hload hcost w hwidth
  · intro A hA
    dsimp only
    intro i _ heavy
    simpa only [Nat.add_assoc] using NativeSelectedParts.children hereditary hsep hK hb G hi hn hD hlarge
      (MomentLP.decode x) hy A hA i heavy

end Lax263307Proofs.NativeSelectedNear
