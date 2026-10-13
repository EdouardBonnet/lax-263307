import Lax263307.RegisteredLP
import Lax455465Proofs.LpCertificateParser

namespace Lax263307Proofs.RegisteredLP

open Lax263307.RegisteredLP
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding

theorem vector_eq (n : ℕ) (input : List ℕ) :
    vector n input = Lax455465Proofs.LpCertificateParser.vector n input := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih =>
    simp only [vector, Lax455465Proofs.LpCertificateParser.vector, ih]
    rfl

theorem vectorFunction_eq (n : ℕ) (input : List ℕ) :
    vectorFunction n input = Lax455465Proofs.LpCertificateParser.vectorFunction n input := by
  simp only [vectorFunction, Lax455465Proofs.LpCertificateParser.vectorFunction, vector_eq]

theorem parse_eq (m n : ℕ) (input : List ℕ) :
    parse m n input = Lax455465Proofs.LpCertificateParser.certificate m n input := by
  cases input with
  | nil => rfl
  | cons tag rest =>
    rcases tag with _ | (_ | (_ | tag)) <;>
      simp only [parse, Lax455465Proofs.LpCertificateParser.certificate, vectorFunction_eq]

theorem parse_encode {m n : ℕ} (c : Certificate m n) (tail : List ℕ) :
    parse m n (encodeCertificate c ++ tail) = some (c, tail) := by
  rw [parse_eq]
  exact Lax455465Proofs.LpCertificateParser.certificate_encode c tail

/--
---
conclusion: Lax263307.RegisteredLP.exists_solver
---
The registered solver returns exactly the encoding of a valid certificate.
Parsing that encoding reconstructs the same certificate, so the total
fallback branch is unreachable on these outputs.
-/
theorem exists_solver : ∃ solve : List ℕ → List ℕ, Lax759944.RamPolytime.RamPolytime solve ∧
    ∀ (m n : ℕ) (P : Program ℚ m n), IsValidCertificate P (certificate solve P) := by
  obtain ⟨solve, hpoly, hsolve⟩ := Lax109476.PolynomialTimeSolver.exists_exact_polynomial_time_solver
  refine ⟨solve, hpoly, ?_⟩
  intro m n P
  obtain ⟨c, hencoded, hvalid⟩ := hsolve m n P
  have hparse : parse m n (encodeCertificate c) = some (c, []) := by
    simpa only [List.append_nil] using parse_encode c []
  simpa only [certificate, hencoded, hparse, Option.map_some, Option.getD_some] using hvalid

end Lax263307Proofs.RegisteredLP
