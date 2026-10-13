import Lax263307.AlmostEmbeddings

/-!
---
title: Almost-embedding transfer with isolated source vertices
type: theorem
---
An almost-embedding of a graph of maximum degree at most $d$ transfers a
host decomposition with bag size at most $w$ to source bags of size at most
$\max\{1,2dw\}$, even if the source has isolated vertices. Restrict to
its nonisolated vertices, apply the connected-carrier transfer, then attach
a singleton leaf bag for each omitted isolated vertex.

# Attribution

The treewidth transfer needed after discarding long routes in Bonnet–Chang,
Lemma 11, extending the no-isolates formulation of Lemma 9.
-/

namespace Lax263307.IsolatedEmbeddingTransfer

open Lax263307.AlmostEmbeddings Lax228581.Treewidth

axiom transfer_decomposition {t n : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (G : SimpleGraph (Fin n)) (E : AlmostEmbedding H G) (d w : ℕ)
    (degree_bound : ∀ v, H.degree v ≤ d)
    (D : TreeDecomposition G) (bag_bound : ∀ i, (D.bag i).card ≤ w) :
    ∃ D' : TreeDecomposition H, ∀ i, (D'.bag i).card ≤ max 1 (2 * d * w)

end Lax263307.IsolatedEmbeddingTransfer
