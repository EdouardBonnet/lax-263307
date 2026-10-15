import Lax263307Proofs.NativeSelectedLP
import Lax263307Proofs.NativeSelectedParts
import Lax263307Proofs.NativeOracleRounds

set_option maxHeartbeats 250000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeOracleCutHeight

open Lax263307 GraphClasses AlgorithmParameters RationalConditioning HeavyRationalConditioning ComputedSeparators
open RoundedOracleSearch

theorem collect_cut_bound {n : ℕ} {ι : Type} [Fintype ι] (order : List ι)
    (parts : ι → Finset (Fin n)) (δ : ℚ) (k : ℕ) (cost : ι → ℚ)
    (query : ι → ℕ → Option (Finset (Fin n)))
    (ht : ∀ i,ComputedRounding.target δ (cost i)≤n+1)
    (vertices : Finset (Fin n)) (u : ℕ)
    (he : ComputedRounding.collect order parts δ k cost query=.cut vertices u) : u≤n := by
  unfold ComputedRounding.collect at he
  cases hfind : order.find? (fun i => (ComputedRounding.answer δ k cost query i).isNone) with
  | none => simp only [hfind] at he; contradiction
  | some i =>
    simp only [hfind,ComputedRounding.Result.cut.injEq] at he
    have h := ht i
    omega

theorem near_cut_bound {n r : ℕ} (flow : List ℕ → List ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D k p b load : ℕ) (y : RationalVector n r)
    (child : (A : Finset (Fin n)) → ℕ → Option (Finset (Fin A.card)))
    (ht : ∀ A,findHeavyConditioning G k p y=some A → ∀ C,
      ComputedRounding.target (1/(D : ℚ)) (∑ v∈C,(NearOracle.costs y A v : ℚ))≤n+1)
    (A C : Finset (Fin n)) (u : ℕ) (he : NativeNearExecution.run flow G D k p b load y child=.cut A C u) : u≤n := by
  unfold NativeNearExecution.run at he
  cases hfind : findHeavyConditioning G k p y with
  | none => simp only [hfind] at he; contradiction
  | some A' =>
    simp only [hfind] at he
    let cs := cuts (step flow G (NearOracle.costs y A') b load k) n Finset.univ
    let query := fun i t => (child (pieces cs i) t).map (fun I => I.image (label (pieces cs i)))
    cases hc : ComputedRounding.collect (NearOracle.order cs.length) (pieces cs) (1/(D : ℚ)) k
        (fun i => ∑ v∈pieces cs i,(NearOracle.costs y A' v : ℚ)) query with
    | found I => rw [hc] at he; contradiction
    | cut vertices bound =>
      rw [hc] at he
      have hu := collect_cut_bound _ _ _ _ _ _ (fun i => ht A' hfind (pieces cs i)) vertices bound hc
      have heq := (NearOracle.Result.cut.inj he).2.2
      omega

theorem normal_height {C : GraphClass} {lp flow : List ℕ → List ℕ} {a K b : ℕ}
    (hsep : NearOracle.SeparatorCorrect C flow a K b) (hK : 0<K) (hb : 0<b)
    (encoded : NativeEncodedLP.Encoded lp) (selected : NativeSelectedLP.Program lp)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : G∈C n)
    (D k R F j : ℕ) (hn : 0<n) (hD : 4≤D) (hlarge : cutoff a K b n D<k)
    (hnR : n≤R) (hkR : k≤R) (hrR : level a K b n D≤R) (hNR : MomentLP.dimension n (level a K b n D)≤R)
    (center : MomentLP.Index n (level a K b n D) → ℚ)
    (hc : ∀ i,NativeRoundedStep.height (center i) (80*(R+1)))
    (child : (A : Finset (Fin n)) → ℕ → Option (Finset (Fin A.card)))
    (normal : Fin (MomentLP.dimension n (level a K b n D)) → ℤ)
    (he : NativeOracleRounds.oracle (r:=level a K b n D) lp flow G D k (sparsity a K b n D) b (load b n D) F child j center=.cut normal) :
    ∀ i,NativeRoundedStep.height (rationalNormal normal i) (NativeOraclePrecision.roundedHeight selected.width R) := by
  let r := level a K b n D
  let H := NativeSelectedLP.certificateHeight selected R
  have hquery := NativeProjectionQueryBounds.uniform_query_size G k r R hnR hkR hrR hNR center hc
  have cert := NativeSelectedLP.certificate_bound selected encoded (MomentLP.program G k r) (ProjectedOracle.raw center) R hquery
  change NativeOracleExecution.reply (r:=r) flow G D k (sparsity a K b n D) b (load b n D) child
    (NativeOracleExecution.projection (r:=r) lp G k D F center)=.cut normal at he
  cases hp : NativeOracleExecution.projection (r:=r) lp G k D F center with
  | reject => rw [hp] at he; change Reply.reject = Reply.cut normal at he; cases he
  | far cut β =>
    rw [hp] at he
    change Reply.cut (RationalCutBuffer.integerNormal cut) = Reply.cut normal at he
    have he := Reply.cut.inj he
    subst normal
    have ha := NativeNormalHeight.far_height (2^H) (MomentLP.program G k r)
      (NativeNodeTolerance.tolerance n D F) _ cert cut β hp
    have hpow : 2*(2^H)^2=2^(2*H+1) := by
      rw [pow_add,Nat.mul_comm 2 H,pow_mul]; norm_num; ring
    rw [hpow] at ha
    intro i
    apply NativeOraclePrecision.height_mono _ _ _ (NativeNormalHeight.cleared_height _ (2*H+1) cut ha i)
    have hmul := Nat.mul_le_mul_right (2*H+1) (Nat.add_le_add_right hNR 1)
    change _≤80*(R+1)+(R+1)*(2*H+1)+2*R+1
    exact hmul.trans (by omega)
  | near x =>
    have feasible := NativeSelectedParts.near_feasible lp encoded G k (ProjectedOracle.raw center)
      (NativeNodeTolerance.tolerance n D F) x hp
    have unit := NativeSelectedParts.selected hsep hK hb G hG hn D k hD hlarge (MomentLP.decode x) feasible
    have targets : ∀ A,findHeavyConditioning G k (sparsity a K b n D) (MomentLP.decode x)=some A →
        ∀ vertices,ComputedRounding.target (1/(D : ℚ)) (∑ v∈vertices,(NearOracle.costs (MomentLP.decode x) A v : ℚ))≤n+1 := by
      intro A hA vertices
      exact NativeSelectedParts.target_bound D (by omega) _ (unit A hA).2.1 vertices
    rw [hp] at he
    change (match NativeNearExecution.run (r:=r) flow G D k (sparsity a K b n D) b (load b n D) (MomentLP.decode x) child with
      | .reject => Reply.reject
      | .found I => Reply.found I
      | .cut A C u => Reply.cut (RationalCutBuffer.integerNormal (rationalNormal (NativeComponentNormal.normal (r:=r) A C u)))) = Reply.cut normal at he
    cases hr : NativeNearExecution.run (r:=r) flow G D k (sparsity a K b n D) b (load b n D) (MomentLP.decode x) child with
    | reject => rw [hr] at he; change Reply.reject = Reply.cut normal at he; cases he
    | found I => rw [hr] at he; change Reply.found I = Reply.cut normal at he; cases he
    | cut A vertices u =>
      rw [hr] at he
      change Reply.cut (RationalCutBuffer.integerNormal (rationalNormal (NativeComponentNormal.normal (r:=r) A vertices u))) = Reply.cut normal at he
      have he := Reply.cut.inj he
      subst normal
      have hu := near_cut_bound flow G D k (sparsity a K b n D) b (load b n D) (MomentLP.decode x) child targets A vertices u hr
      intro i
      exact NativeOraclePrecision.component_height selected.width A vertices u R hu hnR i

end Lax263307Proofs.NativeOracleCutHeight
