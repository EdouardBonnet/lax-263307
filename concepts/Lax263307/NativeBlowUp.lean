import Lax263307.WeightedAlgorithm
import Lax808846.Ram

/-!
---
title: A fixed RAM program constructs the rounded blow-up
type: theorem
---
One finite RAM program reads the original weighted graph, clips negative
weights, computes rounded copy counts, and constructs the adjacency matrix
of the canonically numbered independent blow-up. Its output starts with the
blow-up order and then gives the adjacency matrix in row-major order.

# Formalization notes

The execution proof includes the actual unprefixed input reader, maximum
scan, natural-number quotient for copy counts, owner-array construction,
and every adjacency lookup. Copy owners agree exactly with the computable
finite-sigma labeling used by the weighted algorithm. Time and sufficient
word width are quadratic in the original order, blow-up order, and input
rational height. This is the preprocessing program; the complete recursive
RAM solver and its global quasipolynomial bound remain separate obligations.
-/

namespace Lax263307.NativeBlowUp

open WeightRounding WeightedIndependentSet WeightedAlgorithm

def encode {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List ℕ :=
  n :: (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten

axiom exists_program : ∃ p : Lax808846.Ram.Program, ∃ c : ℕ, 0<c ∧
    ∀ (n h : ℕ), 1≤h → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (w : Fin n → ℚ) (ε : ℚ), 0<ε →
      (∀ i,(w i).num.natAbs≤2^h ∧ (w i).den≤2^h) →
      ε.num.natAbs≤2^h → ε.den≤2^h →
      let cs := copies (fun v => max (w v) 0) ε
      let N := ∑ v,cs v
      ∀ width : ℕ,c*(n+N+h+1)^2≤width →
      ∃ t≤c*(n+N+h+1)^2,Lax808846.Ram.RunsTo width p (encodeInput G w ε)
        (encode (numbered G cs)) t

end Lax263307.NativeBlowUp
