import Lax263307.ConditionalRoutes
import Lax263307.FiniteProductSampling

/-!
---
title: Coupled route sampling with shared vertex images
type: theorem
---
Choose independently a uniform image for every source vertex, then sample
one graph route per source edge from its conditional endpoint law. Positive
outcomes give every route the chosen images of its source endpoints.
Each edge's route has the original route distribution. Routes of two
nonincident source edges have its independent product law, because the four
source endpoints have independently chosen images.

# Formalization notes

The finite outcome is a pair consisting of a source-vertex image assignment
and a route-index assignment. Edge endpoints are given explicitly by two
maps; the marginal assertions require distinct endpoints for a single edge
and four distinct endpoints for a pair. The construction does not assume
independence for incident source edges.

# Attribution

Bonnet–Chang, the coupled sampling construction in Lemma 11.
-/

namespace Lax263307.CoupledRouteSampling

open Lax263307.RouteDistributions Lax263307.ConditionalRoutes
open Lax263307.FiniteProductSampling

noncomputable def uniformWeight (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

noncomputable def jointWeight {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (a b : Fin m → Fin t)
    (φ : Fin t → Fin n) (ψ : Fin m → Fin q) : ℝ :=
  weight (fun _ : Fin t => uniformWeight n) φ *
    weight (fun e => conditional D (φ (a e)) (φ (b e))) ψ

axiom joint_normalized {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t) :
    (∀ φ ψ, 0 ≤ jointWeight D a b φ ψ) ∧
      (∑ φ, ∑ ψ, jointWeight D a b φ ψ) = 1

axiom joint_valid {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t)
    (φ : Fin t → Fin n) (ψ : Fin m → Fin q) (positive : 0 < jointWeight D a b φ ψ) :
    ∀ e, (D.route (ψ e)).head? = some (φ (a e)) ∧
      (D.route (ψ e)).getLast? = some (φ (b e)) ∧
      (D.route (ψ e)).Nodup ∧ (D.route (ψ e)).IsChain G.Adj

axiom single_edge_law {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t)
    (e : Fin m) (nonloop : a e ≠ b e) (i : Fin q) :
    (∑ φ, ∑ ψ, jointWeight D a b φ ψ * (if ψ e = i then (1 : ℝ) else 0)) =
      D.probability i

axiom nonincident_edge_law {n q t m : ℕ} {G : SimpleGraph (Fin n)}
    (D : Distribution G q) (hn : 0 < n) (a b : Fin m → Fin t)
    (e f : Fin m) (nonincident : Function.Injective ![a e, b e, a f, b f]) (i j : Fin q) :
    (∑ φ, ∑ ψ, jointWeight D a b φ ψ *
      ((if ψ e = i then (1 : ℝ) else 0) * (if ψ f = j then (1 : ℝ) else 0))) =
      D.probability i * D.probability j

end Lax263307.CoupledRouteSampling
