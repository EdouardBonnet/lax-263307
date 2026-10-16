import Lax263307.SeparatorComponents
import Lax263307.EdgeSublinearSeparators

/-!
---
title: Balanced closed parts certify a balanced separator
type: lemma
---
A partition of undeleted vertices into parts closed under undeleted graph
edges places each connected component wholly inside one part. If every
part has at most two thirds of the original vertices, the deleted set is
a balanced separator. This permits the parts supplied by repeated cuts.
-/

namespace Lax263307.BalancedPartitions

open SeparatorComponents EdgeSublinearSeparators

axiom balanced_separator {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    {ι : Type} (P : Partition G S ι) (balanced : ∀ i, 3 * (P.vertices i).card ≤ 2 * n) :
    IsBalancedSeparator G S

end Lax263307.BalancedPartitions
