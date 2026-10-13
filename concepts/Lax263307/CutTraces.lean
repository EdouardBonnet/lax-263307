import Lax263307.BalancedPartitions
import Lax263307.RepeatedCutAccounting

/-!
---
title: Repeated cuts yield a balanced light separator
type: theorem
---
Record a cut sequence that removes its right shore at each step. Its
separator is the union of shore intersections; its retained parts are the
exclusive discarded pieces and the final remainder. The right shores are
disjoint, each cut removes a nonempty shore, and no graph edge joins distinct
retained parts. Once the final remainder has at most two thirds of the
original order, the separator is balanced and its cost obeys the cumulative
cut bound. There are at most $n$ cuts.

A cut oracle on every remainder above that size threshold produces such a
trace by induction on remainder cardinality.

# Formalization notes

The small-piece condition bounds $B_i\setminus A_i$, not the full discarded
shore $B_i$, which also contains the separator intersection. The final
parts form the concrete partition used by recursive rounding. These
statements analyze the finite cut sequence; its RAM implementation remains
part of the main algorithm assembly.

# Attribution

Bonnet–Chang, the repeated-cut construction of Lemma 8.
-/

namespace Lax263307.CutTraces

open Lax263307.SeparatorComponents Lax263307.EdgeSublinearSeparators

structure Trace {n : ℕ} (G : SimpleGraph (Fin n)) (start : Finset (Fin n)) (steps : ℕ) where
  remaining : ℕ → Finset (Fin n)
  left : ℕ → Finset (Fin n)
  right : ℕ → Finset (Fin n)
  initial : remaining 0 = start
  cover : ∀ i < steps, left i ∪ right i = remaining i
  next : ∀ i < steps, remaining (i + 1) = left i \ right i
  nonempty : ∀ i < steps, (right i).Nonempty
  small_piece : ∀ i < steps, 2 * (right i \ left i).card ≤ (remaining i).card
  separated : ∀ i < steps, ∀ u ∈ left i \ right i, ∀ v ∈ right i \ left i, ¬G.Adj u v

noncomputable def separator {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) : Finset (Fin n) := Finset.univ.biUnion fun i : Fin q => T.left i ∩ T.right i

def parts {n q : ℕ} {G : SimpleGraph (Fin n)} {start : Finset (Fin n)}
    (T : Trace G start q) : Option (Fin q) → Finset (Fin n)
  | none => T.remaining q
  | some i => T.right i \ T.left i

axiom trace_correct {n q : ℕ} (G : SimpleGraph (Fin n)) (T : Trace G Finset.univ q)
    (finished : 3 * (T.remaining q).card ≤ 2 * n)
    (x : Fin n → ℝ) (nonnegative : ∀ v, 0 ≤ x v) (ρ γ : ℝ) (hρ : 0 ≤ ρ) (hγ : 0 < γ)
    (each_cut : ∀ i < q, Lax263307.RepeatedCutAccounting.cost x (T.left i ∩ T.right i) ≤
      4 * ρ * (T.left i).card * (T.right i).card / γ) :
    q ≤ n ∧ IsBalancedSeparator G (separator T) ∧
      Lax263307.RepeatedCutAccounting.cost x (separator T) ≤ 4 * ρ * (n : ℝ) ^ 2 / γ

axiom light_separator_from_oracle {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin n → ℝ) (nonnegative : ∀ v, 0 ≤ x v) (ρ γ : ℝ) (hρ : 0 ≤ ρ) (hγ : 0 < γ)
    (oracle : ∀ R : Finset (Fin n), 2 * n < 3 * R.card →
      ∃ A B : Finset (Fin n), A ∪ B = R ∧ B.Nonempty ∧ 2 * (B \ A).card ≤ R.card ∧
        (∀ u ∈ A \ B, ∀ v ∈ B \ A, ¬G.Adj u v) ∧
        Lax263307.RepeatedCutAccounting.cost x (A ∩ B) ≤ 4 * ρ * A.card * B.card / γ) :
    ∃ q, ∃ T : Trace G Finset.univ q, q ≤ n ∧ IsBalancedSeparator G (separator T) ∧
      Lax263307.RepeatedCutAccounting.cost x (separator T) ≤ 4 * ρ * (n : ℝ) ^ 2 / γ

end Lax263307.CutTraces
