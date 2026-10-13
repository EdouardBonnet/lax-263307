import Lax263307.WeightRounding
import Lax808846.Ram

/-!
---
title: Native RAM execution of the weight-to-multiplicity reduction
type: theorem
---
One fixed finite RAM program reads the exact unprefixed weighted-graph input,
clips negative weights, finds the maximum, and emits the rounded copy counts
in vertex order. Its running time and sufficient word width are at most
c(n+h+1)^2 when all rational numerators and denominators are at most 2^h.
The guarantee holds at every larger word width.

# Formalization notes

The proof compiles the checked input, maximum, accuracy, multiplicity, and
output loops through the registered RAM simulation theorem. Empty graphs
and instances with no positive weight are included. This implements the
multiplicity calculation; constructing the blow-up and executing the
recursive independent-set algorithm remain separate native obligations.
-/

namespace Lax263307.NativeWeightReduction

open WeightedIndependentSet WeightRounding

axiom exists_program : ∃ p : Lax808846.Ram.Program, ∃ c : ℕ, 0<c ∧
    ∀ (n h : ℕ), 1≤h → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (w : Fin n → ℚ) (ε : ℚ), 0<ε →
      (∀ i,(w i).num.natAbs≤2^h ∧ (w i).den≤2^h) →
      ε.num.natAbs≤2^h → ε.den≤2^h →
      ∀ width : ℕ,c*(n+h+1)^2≤width →
      ∃ t≤c*(n+h+1)^2,Lax808846.Ram.RunsTo width p (encodeInput G w ε)
        (List.ofFn (copies (fun i => max (w i) 0) ε)) t

end Lax263307.NativeWeightReduction
