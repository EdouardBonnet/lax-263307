import Lax263307Proofs.NativeEncodedLP
import Lax263307Proofs.RecursiveAlgorithm
import Lax263307Proofs.ProjectedOracle
import Lax263307Proofs.NativeTrajectoryResources
import Lax263307Proofs.NearOracle

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRecursiveOracle

open Matrix
open Lax263307 GraphClasses AlgorithmParameters ComputedSeparators
open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- Correctness of the chosen projection/flow pair at every recursive node. -/
def OracleCorrect (C : GraphClass) (lp flow : List ℕ → List ℕ) (a K b : ℕ) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G ∈ C n → 0<n →
    ∀ D k h, 4≤D → cutoff a K b n D<k →
    ∀ child, NearOracle.ChildCorrect G D h child →
    ∀ center, ProjectedOracle.Correct G k h a K b D center
      (ProjectedOracle.run lp flow a K b D G k child center)

/-- Choose the actual solvers once, retaining the canonical LP bytes
required by native readers as well as correctness at every recursive node. -/
theorem exists_solvers_with_parts (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0<a) (hA : 0<A) (hclass : PowerBagBounds.HasPowerBagBound C a A) :
    ∃ lp flow K b, Lax759944.RamPolytime.RamPolytime lp ∧ NativeEncodedLP.Encoded lp ∧
      Lax759944.RamPolytime.RamPolytime flow ∧ 0<K ∧ 0<b ∧ NearOracle.SeparatorCorrect C flow a K b ∧ OracleCorrect C lp flow a K b := by
  obtain ⟨lp,hpoly,hlp⟩ := NativeEncodedLP.exists_solver
  obtain ⟨flow,K,b,hflow,hK,hb,hsep,hnear⟩ := NearOracle.exists_oracle_with_parts C hereditary a A ha hA hclass
  refine ⟨lp,flow,K,b,hpoly,hlp,hflow,hK,hb,hsep,?_⟩
  intro n G _ hG hn D k h hD hlarge child hc center
  apply Lax263307Proofs.ProjectedOracle.run_correct lp flow a K b D G k h hK hn hD
    (fun m N P => (hlp m N P).2) child
  intro y hy x hx
  exact hnear n G hG hn D k h hD hlarge y hy x hx child hc

theorem exists_solvers (C : GraphClass) (hereditary : IsHereditary C)
    (a A : ℕ) (ha : 0<a) (hA : 0<A) (hclass : PowerBagBounds.HasPowerBagBound C a A) :
    ∃ lp flow K b, Lax759944.RamPolytime.RamPolytime lp ∧ NativeEncodedLP.Encoded lp ∧
      Lax759944.RamPolytime.RamPolytime flow ∧ 0<K ∧ 0<b ∧ OracleCorrect C lp flow a K b := by
  obtain ⟨lp,flow,K,b,hpoly,hlp,hflow,hK,hb,hsep,ho⟩ :=
    exists_solvers_with_parts C hereditary a A ha hA hclass
  exact ⟨lp,flow,K,b,hpoly,hlp,hflow,hK,hb,ho⟩

theorem search_correct {C : GraphClass} {lp flow : List ℕ → List ℕ} {a K b : ℕ}
    (ho : OracleCorrect C lp flow a K b) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G ∈ C n) (hn : 0<n) (D k h : ℕ) (hD : 4≤D) (hlarge : cutoff a K b n D<k)
    (child : Finset (Fin n) → ℕ → Option (Finset (Fin n))) (hc : NearOracle.ChildCorrect G D h child) :
    ProjectedOracle.SearchCorrect G k h D (ProjectedOracle.search lp flow a K b D G k child) := by
  exact Lax263307Proofs.ProjectedOracle.search_correct lp flow a K b D G k h hn (by omega) child
    (ho n G hG hn D k h hD hlarge child hc)

def child {n : ℕ} (lp flow : List ℕ → List ℕ) (a K b D fuel : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) (t : ℕ) : Option (Finset (Fin n)) :=
  (RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G S) t).map
    (fun I => I.image (label S))

theorem child_correct {C : GraphClass} (hereditary : IsHereditary C)
    {lp flow : List ℕ → List ℕ} {a K b : ℕ} (ho : OracleCorrect C lp flow a K b)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G ∈ C n) (hn : 1<n)
    (D fuel : ℕ) (hD : 4≤D) (hdepth : RecursionDepth.depth n≤fuel+1) :
    NearOracle.ChildCorrect G D fuel (child lp flow a K b D fuel G) := by
  intro S hS t
  have hclass := hereditary S.card n (restriction G S) G hG
    ⟨Lax263307Proofs.ComputedSeparators.embedding G S⟩
  have hdep := RecursionDepth.balanced_decrease n S.card hn hS
  have hh := Lax263307Proofs.RecursiveAlgorithm.attempt_correct C hereditary lp flow a K b D hD
    (fun m H _ hH hm j h hj query hquery => search_correct ho H hH hm D j h hD hj query hquery)
    fuel (restriction G S) hclass (by omega) t
  dsimp only [child]
  cases he : RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G S) t with
  | some I =>
    rw [he] at hh
    change _ ∧ _ ∧ _
    refine ⟨Lax263307Proofs.RecursiveAlgorithm.image_subset S I,
      Lax263307Proofs.RecursiveAlgorithm.image_independent G S I hh.1,?_⟩
    rw [Finset.card_image_of_injective _ (label S).injective]
    exact hh.2
  | none =>
    rw [he] at hh
    exact Lax263307Proofs.RecursiveAlgorithm.restriction_bound G S t hh

/-- Every cut of the actual recursive oracle is nonzero. This supplies
all iterations' numeric-height and positive quadratic-form hypotheses. -/
theorem cut_nonzero {C : GraphClass} (hereditary : IsHereditary C)
    {lp flow : List ℕ → List ℕ} {a K b : ℕ} (ho : OracleCorrect C lp flow a K b)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G ∈ C n) (hn : 1<n)
    (D k fuel : ℕ) (hD : 4≤D) (hlarge : cutoff a K b n D<k) (hdepth : RecursionDepth.depth n≤fuel+1) :
    ∀ j center normal, (fun (_ : ℕ) center => ProjectedOracle.run lp flow a K b D G k
      (child lp flow a K b D fuel G) center) j center = RoundedOracleSearch.Reply.cut normal →
      ∃ i,normal i≠0 := by
  intro j center normal he
  have hc := ho n G hG (by omega) D k fuel hD hlarge _ (child_correct hereditary ho G hG hn D fuel hD hdepth) center
  dsimp only at he
  rw [he] at hc
  exact hc.1

/-- The numeric height and quadratic-form guards now hold for the
actual recursive search trajectory, using the recursive semantic proof. -/
theorem trajectory_guards {C : GraphClass} (hereditary : IsHereditary C)
    {lp flow : List ℕ → List ℕ} {a K b : ℕ} (ho : OracleCorrect C lp flow a K b)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G ∈ C n) (hn : 1<n)
    (D k fuel R j : ℕ) (hD : 4≤D) (hlarge : cutoff a K b n D<k)
    (hdepth : RecursionDepth.depth n≤fuel+1) (hN : MomentLP.dimension n (level a K b n D)≤R) (hj : j≤R) :
    let oracle := fun (_ : ℕ) center => ProjectedOracle.run lp flow a K b D G k
      (child lp flow a K b D fuel G) center
    (∀ i l,NativeRoundedStep.height ((RoundedOracleSearch.trajectory oracle j).1 i l) (80*(R+1))) ∧
    (∀ i,NativeRoundedStep.height ((RoundedOracleSearch.trajectory oracle j).2 i) (80*(R+1))) ∧
    ∀ normal,oracle j (RoundedOracleSearch.trajectory oracle j).2=.cut normal →
      0<dotProduct (RoundedOracleSearch.rationalNormal normal)
        ((RoundedOracleSearch.trajectory oracle j).1 *ᵥ RoundedOracleSearch.rationalNormal normal) := by
  dsimp only
  let oracle := fun (_ : ℕ) center => ProjectedOracle.run lp flow a K b D G k
    (child lp flow a K b D fuel G) center
  have hdim := CoordinateCatalog.catalog_two n (level a K b n D) (by omega : 0<n)
  have hnz := cut_nonzero hereditary ho G hG hn D k fuel hD hlarge hdepth
  have heights := NativeTrajectoryResources.state_height hdim oracle hnz R j hN hj
  exact ⟨heights.1,heights.2,fun normal he => NativeTrajectoryResources.update_positive hdim oracle hnz j normal he⟩

end Lax263307Proofs.NativeRecursiveOracle
