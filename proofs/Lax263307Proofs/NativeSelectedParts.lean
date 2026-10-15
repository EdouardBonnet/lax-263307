import Lax263307Proofs.NativeRecursiveDomain
import Lax263307Proofs.NativeRecursiveOracle
import Lax263307Proofs.MomentLP

namespace Lax263307Proofs.NativeSelectedParts

open Lax263307 GraphClasses AlgorithmParameters RationalConditioning HeavyRationalConditioning ComputedSeparators LinearRelaxation

/-- The selected successful conditioning gives exactly the unit costs and
balanced computed pieces needed by the recursive execution domain. -/
theorem selected {C : GraphClass} {flow : List ℕ → List ℕ} {a K b : ℕ}
    (hsep : Lax263307Proofs.NearOracle.SeparatorCorrect C flow a K b)
    (hK : 0<K) (hb : 0<b) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G∈C n) (hn : 0<n) (D k : ℕ) (hD : 4≤D) (hlarge : cutoff a K b n D<k)
    (y : RationalVector n (level a K b n D))
    (hy : LinearRelaxation.IsFeasible G k (level a K b n D) (realVector y))
    (A : Finset (Fin n)) (hfind : findHeavyConditioning G k (sparsity a K b n D) y=some A) :
    A.card≤level a K b n D ∧ (∀ v,NearOracle.costs y A v≤1) ∧
      let cs := cuts (step flow G (NearOracle.costs y A) b (load b n D) k) n Finset.univ
      ∀ i,3*(pieces cs i).card≤2*n := by
  have bud := AlgorithmParameters.budgets hK hb hD hlarge
  obtain ⟨A',choice,hsize,hmoment,hpositive,hcosts,hmass,hedge⟩ :=
    HeavyRationalConditioning.search_correct G k (level a K b n D) (sparsity a K b n D) y hy hn
      (by omega) bud.2.2.1 bud.2.1 bud.2.2.2.2.2.2.1
  have heq : A'=A := Option.some.inj (choice.symm.trans hfind)
  subst A'
  let x := NearOracle.costs y A
  have cast (v : Fin n) : (x v : ℝ)=conditioned (realVector y) A v :=
    Lax263307Proofs.NearOracle.costs_cast y A (fun v => (hcosts v).1) v
  have hunit (v : Fin n) : (x v : ℝ)≤1 := by rw [cast]; exact (hcosts v).2
  have hsum : (∑ v,(x v : ℝ))≤k := by simp only [cast]; exact hmass.le
  have hedge' : Entropy.edgeCost G (fun v => (x v : ℝ))≤(k : ℝ)^2/(sparsity a K b n D) := by
    simpa only [cast] using hedge
  obtain ⟨hlen,hbalanced,hlight,P,hverts,hparts⟩ := hsep n G hG hn x k (sparsity a K b n D) (load b n D)
    (by omega) bud.2.1 bud.1 hunit hsum hedge' bud.2.2.2.2.2.2.2.1 bud.2.2.2.2.2.2.2.2
  refine ⟨hsize,?_,?_⟩
  · intro v
    have h := hunit v
    exact_mod_cast h
  · dsimp only
    intro i
    rw [←hverts i]
    exact hparts i

theorem target_bound {n : ℕ} (D : ℕ) (hD : 0<D) (x : Fin n → ℚ≥0) (hx : ∀ v,x v≤1)
    (vertices : Finset (Fin n)) :
    ComputedRounding.target (1/(D : ℚ)) (∑ v∈vertices,(x v : ℚ))≤n+1 := by
  have hnonnegative : (0 : ℚ)≤∑ v∈vertices,(x v : ℚ) := Finset.sum_nonneg (fun v _ => by positivity)
  by_cases hz : (∑ v∈vertices,(x v : ℚ))=0
  · simp [ComputedRounding.target,hz]
  · have ht := NativeChildResources.target_le (1/(D : ℚ)) _ vertices.card (by positivity)
      (lt_of_le_of_ne hnonnegative (Ne.symm hz)) (NativeChildResources.component_cost_le x vertices hx)
    exact ht.trans ((NativeMaskUnpack.card_bound vertices).trans (Nat.le_succ n))

theorem children {C : GraphClass} (hereditary : IsHereditary C)
    {flow : List ℕ → List ℕ} {a K b N frameSize capacity fuel n k cursor D : ℕ}
    (hsep : Lax263307Proofs.NearOracle.SeparatorCorrect C flow a K b) (hK : 0<K) (hb : 0<b)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hi : NativeRecursiveDomain.eligible C N frameSize capacity (fuel+1) n G k cursor)
    (hn : 1<n) (hD : 4≤D) (hlarge : cutoff a K b n D<k)
    (y : RationalVector n (level a K b n D))
    (hy : LinearRelaxation.IsFeasible G k (level a K b n D) (realVector y))
    (A : Finset (Fin n)) (hfind : findHeavyConditioning G k (sparsity a K b n D) y=some A) :
    let costs := NearOracle.costs y A
    let cs := cuts (step flow G costs b (load b n D) k) n Finset.univ
    ∀ i,(1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈pieces cs i,(costs v : ℚ)) →
      NativeRecursiveDomain.eligible C N frameSize capacity fuel (pieces cs i).card (restriction G (pieces cs i))
        (ComputedRounding.target (1/(D : ℚ)) (∑ v∈pieces cs i,(costs v : ℚ))) (cursor+frameSize) := by
  have parts := selected hsep hK hb G hi.1 (by omega) D k hD hlarge y hy A hfind
  dsimp only
  intro i heavy
  exact NativeRecursiveDomain.heavy_child hereditary G hi hn (by omega) (NearOracle.costs y A) parts.2.1
    _ (parts.2.2 i) heavy

theorem near_bound {m N : ℕ} (M : ℕ) (P : Lax109476.LinearProgram.Program ℚ m N) (ρ : ℚ)
    (certificate : Lax109476.RationalCertificates.Certificate (m+(N+N)) (N+1))
    (hc : NativeProjectionResult.CertificateBounded M certificate) (x : Fin N → ℚ)
    (hnear : RationalProjection.classify P ρ certificate=.near x) :
    ∀ i,NativeSignedArithmetic.Bounded M (x i) := by
  cases certificate with
  | infeasible y => simp [RationalProjection.classify] at hnear
  | unbounded z y => simp [RationalProjection.classify] at hnear
  | optimal z y =>
    dsimp only [RationalProjection.classify] at hnear
    split at hnear
    · cases hnear
      intro i
      exact hc.1 _
    · contradiction

theorem near_feasible {n r : ℕ} (lp : List ℕ → List ℕ) (hlp : NativeEncodedLP.Encoded lp)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) (center : MomentLP.Index n r → ℚ) (ρ : ℚ)
    (x : MomentLP.Index n r → ℚ)
    (hnear : RationalProjection.classify (MomentLP.program G k r) ρ
      (RegisteredLP.certificate lp (DistanceProjection.distanceProgram (MomentLP.program G k r) center))=.near x) :
    LinearRelaxation.IsFeasible G k r (realVector (MomentLP.decode x)) := by
  have correct := Lax263307Proofs.RationalProjection.classify_correct (MomentLP.program G k r) center ρ
    (RegisteredLP.certificate lp (DistanceProjection.distanceProgram (MomentLP.program G k r) center))
    (hlp _ _ _).2
  rw [hnear] at correct
  have feasible := (Lax263307Proofs.MomentLP.primal_characterization G k r
    (fun i => (x i : ℝ))).mp correct.1
  exact feasible

end Lax263307Proofs.NativeSelectedParts
