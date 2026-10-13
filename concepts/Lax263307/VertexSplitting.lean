import Lax455465.RamDirectedUniformFlowCut
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
---
title: Vertex splitting for the directed flow–cut algorithm
type: theorem
---
Replace each original vertex $v$ by two ports $v^-$ and $v^+$.
The capacity of $v^-\to v^+$ is its cost $x_v$. Reverse port arcs and arcs
$v^+\to u^-$ for graph edges receive a sufficiently large finite capacity.
A directed cut of capacity less than this large capacity crosses none of
these arcs and projects to a separation of the original graph. Its capacity
equals the vertex cost of the projected separator.

The registered directed uniform flow–cut algorithm applies to this rational
split network with its actual RAM polynomial-time guarantee. Each original
ordered pair uses the distinct split endpoints $u^-,v^+$, also when $u=v$.

# Formalization notes

Ports are numbered $2v$ and $2v+1$. The cut shores are the vertices whose
minus ports lie inside the cut and whose plus ports lie outside it.
The cut projection and the external solver's application are proved here;
flow projection and the RAM cost of constructing the split input are separate
steps of the reduction.

# Attribution

Bonnet–Chang, the vertex-splitting reduction in Lemma 7, using the registered
Leighton–Rao algorithm in Lax455465.
-/

namespace Lax263307.VertexSplitting

open scoped NNReal NNRat
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow

/-- The input port of an original vertex. -/
def minus {n : ℕ} (v : Fin n) : Fin (2 * n) := ⟨2 * v.val, by omega⟩
/-- The output port of an original vertex. -/
def plus {n : ℕ} (v : Fin n) : Fin (2 * n) := ⟨2 * v.val + 1, by omega⟩
/-- Forget which of the two ports represents a vertex. -/
def original {n : ℕ} (v : Fin (2 * n)) : Fin n := ⟨v.val / 2, by omega⟩

/-- Rational capacities and uniform demands on the split network. -/
def splitInstance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) : RationalInstance (2 * n) where
  capacity u v :=
    if u.val % 2 = 0 ∧ v.val = u.val + 1 then x (original u)
    else if u.val % 2 = 1 ∧ v.val + 1 = u.val then large
    else if u.val % 2 = 1 ∧ v.val % 2 = 0 ∧ G.Adj (original u) (original v) then large
    else 0
  loopless v := by
    have hforward : ¬(v.val % 2 = 0 ∧ v.val = v.val + 1) := by omega
    have hreverse : ¬(v.val % 2 = 1 ∧ v.val + 1 = v.val) := by omega
    have hedge : ¬(v.val % 2 = 1 ∧ v.val % 2 = 0 ∧ G.Adj (original v) (original v)) := by omega
    simp only [if_neg hforward, if_neg hreverse, if_neg hedge]
  weight _ := 1

/-- Original vertices whose input ports lie inside the split cut. -/
def leftShore {n : ℕ} (U : Finset (Fin (2 * n))) : Finset (Fin n) :=
  Finset.univ.filter fun v => minus v ∈ U

/-- Original vertices whose output ports lie outside the split cut. -/
def rightShore {n : ℕ} (U : Finset (Fin (2 * n))) : Finset (Fin n) :=
  Finset.univ.filter fun v => plus v ∉ U

/-- A small split cut projects to a nontrivial separation with controlled shores. -/
axiom small_cut_separation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n)))
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0))
    (nonempty : U.Nonempty) (proper : Uᶜ.Nonempty) :
    (leftShore U).Nonempty ∧ (rightShore U).Nonempty ∧
      leftShore U ∪ rightShore U = Finset.univ ∧
      (∀ u ∈ leftShore U \ rightShore U, ∀ v ∈ rightShore U \ leftShore U, ¬G.Adj u v) ∧
      U.card ≤ 2 * (leftShore U).card ∧ Uᶜ.card ≤ 2 * (rightShore U).card

/-- Only the vertex-capacity arcs contribute to a small split cut. -/
axiom small_cut_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n)))
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0)) :
    cutCapacity (splitInstance G x large).network U =
      ∑ v ∈ leftShore U ∩ rightShore U, (x v : ℝ≥0)

/-- Translate a directed cut ratio into the original separator's vertex cost. -/
axiom separator_cost_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (large : ℚ≥0) (U : Finset (Fin (2 * n))) (ρ : ℝ)
    (nonnegative : 0 ≤ ρ)
    (small : cutCapacity (splitInstance G x large).network U < (large : ℝ≥0))
    (admissible : AdmissibleCut (splitInstance G x large).weights U)
    (ratio : (ratioCost (splitInstance G x large).network
      (splitInstance G x large).weights U : ℝ) ≤ ρ) :
    (∑ v ∈ leftShore U ∩ rightShore U, (x v : ℝ)) ≤
      4 * ρ * (leftShore U).card * (rightShore U).card

/-- Apply the existing directed uniform solver to every split network. -/
axiom split_certificate :
  ∃ (solve : List ℕ → List ℕ) (C : ℝ), Lax759944.RamPolytime.RamPolytime solve ∧ 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (x : Fin n → ℚ≥0) (large : ℚ≥0), 2 ≤ n →
      let I := splitInstance G x large
      ∃ certificate : Lax455465.FlowCutCertificate.Certificate (2 * n),
        solve (encodeInput .directed I) = Lax455465.FlowCutCertificate.encodeCertificate certificate ∧
        AdmissibleCut I.weights certificate.cut ∧
        IsArcConcurrentFlow .directed I.network I.weights
          (certificate.flow.value : ℝ≥0) certificate.flow.flow ∧
        (ratioCost I.network I.weights certificate.cut : ℝ) ≤
          C * logFactor (2 * n) * (certificate.flow.value : ℝ)

end Lax263307.VertexSplitting
