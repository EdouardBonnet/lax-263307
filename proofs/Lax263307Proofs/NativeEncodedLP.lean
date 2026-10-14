import Lax263307Proofs.RegisteredLP
import Lax263307Proofs.NativeSignedArithmetic

namespace Lax263307Proofs.NativeEncodedLP

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.RegisteredLP

/-- A canonical solver contract retaining the exact byte-level witness,
so native certificate readers and functional parsing use the same result. -/
def Encoded (solve : List ℕ → List ℕ) : Prop := ∀ (m n : ℕ) (P : Program ℚ m n),
  solve (encodeProgram P)=encodeCertificate (certificate solve P) ∧
    IsValidCertificate P (certificate solve P)

theorem certificate_eq {m n : ℕ} (solve : List ℕ → List ℕ) (P : Program ℚ m n)
    (c : Certificate m n) (hc : solve (encodeProgram P)=encodeCertificate c) :
    certificate solve P=c := by
  have hparse : parse m n (encodeCertificate c)=some (c,[]) := by
    simpa only [List.append_nil] using Lax263307Proofs.RegisteredLP.parse_encode c []
  simp only [certificate,hc,hparse,Option.map_some,Option.getD_some]

theorem exists_solver : ∃ solve : List ℕ → List ℕ,
    Lax759944.RamPolytime.RamPolytime solve ∧ Encoded solve := by
  obtain ⟨solve,hpoly,hsolve⟩ := Lax109476.PolynomialTimeSolver.exists_exact_polynomial_time_solver
  refine ⟨solve,hpoly,?_⟩
  intro m n P
  obtain ⟨c,hencoded,hvalid⟩ := hsolve m n P
  rw [certificate_eq solve P c hencoded]
  exact ⟨hencoded,hvalid⟩

theorem coordinate_bounds (M n : ℕ) (x : Fin n → ℚ)
    (hx : ∀ v∈encodeVector x,v≤M) (i : Fin n) : NativeSignedArithmetic.Bounded M (x i) := by
  have hmem (v : ℕ) (hv : v∈encodeRational (x i)) : v∈encodeVector x := by
    apply List.mem_flatMap.mpr
    exact ⟨x i,List.mem_ofFn.mpr ⟨i,rfl⟩,hv⟩
  exact ⟨hx _ (hmem _ (by simp [encodeRational])),hx _ (hmem _ (by simp [encodeRational]))⟩

end Lax263307Proofs.NativeEncodedLP
