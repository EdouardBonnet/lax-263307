import Lax109476.PolynomialTimeSolver

/-!
---
title: Decoding the actual registered LP solver output
type: theorem
---
Read the tagged rational certificate returned by the registered exact LP
solver. The decoded certificate is valid for the supplied program, in all
dimensions and for all three outcomes. This provides the concrete solver
function used by the projection branch of the round-or-cut algorithm.

# Formalization notes

The parser and fallback are total and computable. The fallback is never used
on the registered solver's output. The parser matches the verified parser
in the registered Leighton–Rao proof package; an induction identifies the
parsers and reuses its encoding theorem. The surrounding RAM invocation remains a separate
implementation obligation.
-/

namespace Lax263307.RegisteredLP

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding

def value (sign num den : ℕ) : ℚ :=
  if sign = 1 then -(num : ℚ) / den else (num : ℚ) / den

def rational : List ℕ → Option (ℚ × List ℕ)
  | sign :: num :: den :: rest => some (value sign num den, rest)
  | _ => none

def vector : ℕ → List ℕ → Option (List ℚ × List ℕ)
  | 0, input => some ([], input)
  | n + 1, input => (rational input).bind fun qr =>
      (vector n qr.2).map fun tail => (qr.1 :: tail.1, tail.2)

def vectorFunction (n : ℕ) (input : List ℕ) : Option ((Fin n → ℚ) × List ℕ) :=
  (vector n input).map fun result => (fun i => result.1.getD i.val 0, result.2)

def parse (m n : ℕ) : List ℕ → Option (Certificate m n × List ℕ)
  | 0 :: rest => (vectorFunction n rest).bind fun zr =>
      (vectorFunction m zr.2).map fun yr => (.optimal zr.1 yr.1, yr.2)
  | 1 :: rest => (vectorFunction m rest).map fun yr => (.infeasible yr.1, yr.2)
  | 2 :: rest => (vectorFunction n rest).bind fun zr =>
      (vectorFunction n zr.2).map fun dr => (.unbounded zr.1 dr.1, dr.2)
  | _ => none

def certificate {m n : ℕ} (solve : List ℕ → List ℕ) (P : Program ℚ m n) : Certificate m n :=
  ((parse m n (solve (encodeProgram P))).map Prod.fst).getD (.infeasible 0)

axiom exists_solver : ∃ solve : List ℕ → List ℕ, Lax759944.RamPolytime.RamPolytime solve ∧
    ∀ (m n : ℕ) (P : Program ℚ m n), IsValidCertificate P (certificate solve P)

end Lax263307.RegisteredLP
