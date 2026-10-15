import Lax920634.ConstructionSize
import Lax920634.SubcubicConstruction
import Lax920634.ExplicitTreewidth

/-!
---
title: Controlled-size subcubic source graphs of linear treewidth
type: lemma
---
The registered deterministic subcubic family supplies fixed positive
constants for width and size overshoot. For every requested order, choose a
source graph above the request and below a fixed multiple of the request
plus one, with order bounded by the width constant times treewidth plus one.
The upper size bound is needed to meet the route-sampling budgets.

# Attribution

Lax920634's registered subcubic construction, size bound, and explicit
linear-treewidth theorem; the source family used in Bonnet–Chang, Lemma 10.
-/

namespace Lax263307.SourceGraphs

open Lax920634.ZigZagConstruction Lax920634.GraphEncoding Lax920634.SeedSearch
open Lax920634.EdgeExpansion Lax228581.Treewidth

axiom controlled_family : ∃ widthConstant sizeConstant : ℕ,
    0 < widthConstant ∧ 0 < sizeConstant ∧
    ∀ request : ℕ, ∃ n, ∃ H : SimpleGraph (Fin n), request ≤ n ∧
      n ≤ sizeConstant * (request + 1) ∧ IsSubcubic H ∧
      n ≤ widthConstant * (treewidth H + 1)

end Lax263307.SourceGraphs
