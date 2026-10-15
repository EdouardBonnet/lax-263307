import Lax263307Proofs.NativeNodeExecution
import Lax263307Proofs.NativeChildResources
import Lax263307Proofs.RecursionDepth
import Lax263307Proofs.ComputedSeparators

namespace Lax263307Proofs.NativeRecursiveDomain

open Lax263307 GraphClasses ComputedSeparators NativeNodeProtocol

/-- The semantic and numerical domain of actual recursive calls. -/
def eligible (C : GraphClass) (N frameSize capacity : ℕ) : Eligible :=
  fun fuel n G k cursor => G∈C n ∧ 0<n ∧ n≤N ∧ 0<k ∧ k≤n ∧
    RecursionDepth.depth n≤fuel ∧ cursor+fuel*frameSize≤capacity

theorem root {C : GraphClass} {N frameSize capacity : ℕ} (G : SimpleGraph (Fin N))
    (hG : G∈C N) (hN : 0<N) (hstack : RecursionDepth.depth N*frameSize≤capacity)
    (k : ℕ) (hk : 0<k) (hkN : k≤N) :
    eligible C N frameSize capacity (RecursionDepth.depth N) N G k 0 :=
  ⟨hG,hN,Nat.le_refl _,hk,hkN,Nat.le_refl _,by simpa using hstack⟩

/-- Balanced positive-order children inherit class membership, available
fuel, target range and stack capacity. -/
theorem child {C : GraphClass} (hereditary : IsHereditary C)
    {N frameSize capacity fuel n k cursor : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hi : eligible C N frameSize capacity (fuel+1) n G k cursor) (hn : 1<n)
    (vertices : Finset (Fin n)) (hbalanced : 3*vertices.card≤2*n)
    (hvertices : 0<vertices.card) (target : ℕ) (ht : 0<target) (htv : target≤vertices.card) :
    eligible C N frameSize capacity fuel vertices.card (restriction G vertices) target (cursor+frameSize) := by
  have hclass := hereditary vertices.card n (restriction G vertices) G hi.1 ⟨Lax263307Proofs.ComputedSeparators.embedding G vertices⟩
  have hdep := Lax263307Proofs.RecursionDepth.balanced_decrease n vertices.card hn hbalanced
  have hdepth := hi.2.2.2.2.2.1
  refine ⟨hclass,hvertices,(NativeMaskUnpack.card_bound vertices).trans hi.2.2.1,ht,htv,by omega,?_⟩
  have heq : (cursor+frameSize)+fuel*frameSize=cursor+(fuel+1)*frameSize := by ring
  rw [heq]
  exact hi.2.2.2.2.2.2

/-- Only heavy components enter recursion. Empty and zero-cost components
need no recursive domain proof because the native collector skips them. -/
theorem heavy_child {C : GraphClass} (hereditary : IsHereditary C)
    {N frameSize capacity fuel n k cursor D : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hi : eligible C N frameSize capacity (fuel+1) n G k cursor) (hn : 1<n) (hD : 0<D)
    (x : Fin n → ℚ≥0) (hx : ∀ v,x v≤1) (vertices : Finset (Fin n))
    (hbalanced : 3*vertices.card≤2*n)
    (hheavy : (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈vertices,(x v : ℚ))) :
    eligible C N frameSize capacity fuel vertices.card (restriction G vertices)
      (ComputedRounding.target (1/(D : ℚ)) (∑ v∈vertices,(x v : ℚ))) (cursor+frameSize) := by
  have hc := NativeChildResources.active_child D k x vertices hD hx hheavy
  exact child hereditary G hi hn vertices hbalanced hc.1 _ (by unfold ComputedRounding.target; omega) hc.2.1

end Lax263307Proofs.NativeRecursiveDomain
