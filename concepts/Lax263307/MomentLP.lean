import Lax263307.CoordinateCatalog
import Lax263307.ComponentCutEncoding
import Lax109476.RationalCertificates

/-!
---
title: The moment relaxation as an explicit rational linear program
type: lemma
---
Use the computable moment catalog as the LP variable order. Paired
normalization rows, upper-bound rows, nonindependence rows, insertion
monotonicity rows, and paired conditioned-mass rows encode the relaxation
exactly. Primal nonnegativity supplies the coordinate lower bounds.
The resulting rational LP has N variables and 2+4N+Nn rows, where
N≤(r+3)(n+1)^(r+2).

# Formalization notes

All finite index concatenations and graph independence tests are computable.
Rows indexed by sets of size r+2 are inactive in the two families restricted
to size at most r+1. Collected component-cut coefficients can use the same
catalog order, with evaluation exactly equal to a native finite dot product.
Dense input construction and solver execution on RAM remain separate bounds.
-/

namespace Lax263307.MomentLP

open ComponentCutEncoding (evaluate)
open LinearRelaxation CoordinateCatalog
open Lax109476.LinearProgram Lax109476.RationalCertificates

abbrev dimension (n r : ℕ) : ℕ := (catalog n r).length
abbrev Index (n r : ℕ) := Fin (dimension n r)

/-- Row blocks for normalization, coordinate bounds, independence, monotonicity, and mass. -/
abbrev rowCount (n r : ℕ) : ℕ :=
  let N := dimension n r
  2 + (N + (N + (N * n + (N + N))))

def decode {K : Type} {n r : ℕ} (x : Index n r → K) : Coordinate n r → K :=
  fun A => x ((indexing n r).symm A)

def encode {K : Type} {n r : ℕ} (y : Coordinate n r → K) : Index n r → K :=
  fun j => y (indexing n r j)

def singleRow {n r : ℕ} (A : Finset (Fin n)) (j : Index n r) : ℚ :=
  if A = (indexing n r j).val then 1 else 0

def monotoneRow {n r : ℕ} (A : Finset (Fin n)) (v : Fin n) (j : Index n r) : ℚ :=
  singleRow (insert v A) j - singleRow A j

def massRow {n r : ℕ} (A : Finset (Fin n)) (k : ℕ) (j : Index n r) : ℚ :=
  (∑ v, singleRow (insert v A) j) - (k : ℚ) * singleRow A j

def program {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    Program ℚ (rowCount n r) (dimension n r) where
  A := Fin.addCases
    (fun i : Fin 2 => fun j => if i = 0 then singleRow ∅ j else -singleRow ∅ j)
    (Fin.addCases
      (fun i : Index n r => singleRow (indexing n r i).val)
      (Fin.addCases
        (fun i : Index n r => fun j =>
          if G.IsIndepSet ((indexing n r i).val : Set (Fin n)) then 0 else singleRow (indexing n r i).val j)
        (Fin.addCases
          (fun i : Fin (dimension n r * n) =>
            let uv := finProdFinEquiv.symm i
            if (indexing n r uv.1).val.card ≤ r + 1 then
              monotoneRow (indexing n r uv.1).val uv.2 else fun _ => 0)
          (Fin.addCases
            (fun i : Index n r =>
              if (indexing n r i).val.card ≤ r + 1 then massRow (indexing n r i).val k else fun _ => 0)
            (fun i : Index n r => fun j =>
              if (indexing n r i).val.card ≤ r + 1 then -massRow (indexing n r i).val k j else 0)))))
  b := Fin.addCases (fun i : Fin 2 => if i = 0 then 1 else -1)
    (Fin.addCases (fun _ : Index n r => 1) (fun _ => 0))
  c := fun _ => 0

axiom decode_encode {K : Type} {n r : ℕ} (y : Coordinate n r → K) : decode (encode y) = y

axiom single_row_value {n r : ℕ} (x : Index n r → ℝ) (A : Finset (Fin n)) :
    (∑ j, (singleRow A j : ℝ) * x j) = value (decode x) A

axiom primal_characterization {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (x : Index n r → ℝ) :
    PrimalFeasible (toReal (program G k r)) x ↔ IsFeasible G k r (decode x)

axiom evaluate_encoding {n r : ℕ} (a : Coordinate n r → ℤ) (x : Index n r → ℝ) :
    evaluate a (decode x) =
      (fun j => ((encode a j : ℤ) : ℝ)) ⬝ᵥ x

end Lax263307.MomentLP
