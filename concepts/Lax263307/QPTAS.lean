import Lax263307.IndependentSetProblem
import Lax263307.QPTASRuntime

/-!
---
title: A QPTAS for maximum-weight independent set
type: definition
---
A graph class admits a deterministic QPTAS for maximum-weight independent
set when its optimization problem has a QPTAS in the registered sense of
lax-213208. One fixed program works for every integer precision $k>0$ and
returns an independent set with weight at least $\mathrm{OPT}/(1+1/k)$.
For each fixed $k$, its running time is quasipolynomial in the binary input
size. Both the input words and the running time obey the archive's uniform
word-width convention.

The instance is the standard structural encoding of the graph order,
adjacency matrix, and rational vertex weights. The scheme's precision is
supplied separately. Neither a separator nor class recognition is supplied.

# Formalization notes

`HasQPTAS` is a specialization of `Lax213208.QPTAS.QPTAS`, without a separate
execution or complexity definition. The proof constructs a structured command,
adapts the structural input to the existing weighted algorithm, and applies
lax-62's `Codegen.computesInTime_of_spec` directly. The stronger original
accuracy-dependent estimate remains available internally in `QPTASRuntime`.
-/

namespace Lax263307.QPTAS

open GraphClasses IndependentSetProblem
open Lax213208.QPTAS (QPTAS)

/-- The registered approximation-scheme predicate specialized to MWIS. -/
def HasQPTAS (C : GraphClass) : Prop :=
  ∃ alg, QPTAS (problem := problem) alg (instances C)

end Lax263307.QPTAS
