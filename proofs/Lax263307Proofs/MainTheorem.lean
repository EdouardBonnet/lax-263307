import Lax263307.MainTheorem
import Lax263307Proofs.ArchiveQptas

namespace Lax263307Proofs.MainTheorem

open Lax263307 GraphClasses EdgeSublinearSeparators IndependentSetProblem
open Lax213208.QPTAS (QPTAS)

/--
---
conclusion: Lax263307.MainTheorem.exists_qptas
---
Establish the registered `QPTAS` predicate directly for MWIS. The proof
uses one structured program for all integer precisions, verifies its structural
input reader and approximation ratio, and applies lax-62's compilation theorem
directly. The checked source estimates imply the archive's uniform execution
and quasipolynomial-time bounds.
-/
theorem exists_qptas (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ alg, QPTAS (problem := problem) alg (instances C) :=
  ArchiveQptas.exists_qptas C hereditary separators

end Lax263307Proofs.MainTheorem
