import Lax263307Proofs.NativeProjectionOracle
import Lax263307Proofs.NativeProjectionCut

set_option maxRecDepth 10000
set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeIntegerProjection

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307.DistanceProjection Lax263307.RationalProjection
open NativeDistanceData

theorem classify_guard (B h m n : ℕ) (P : Program ℚ m n) (ρ : ℚ)
    (c : Certificate (m+(n+n)) (n+1))
    (hc : NativeProjectionResult.CertificateBounded (2^h) c)
    (hB : 2^(NativeCutResources.wordExponent n (2*h+1))≤B) :
    NativeProjectionCut.Guard B (2^(2*h+1)) (classify P ρ c) := by
  cases c with
  | optimal z y =>
    by_cases hnear : distance z≤ρ
    · simp only [classify,if_pos hnear,NativeProjectionCut.Guard]
    simp only [classify,if_neg hnear,NativeProjectionCut.Guard]
    have hh : 2*(2^h)^2=2^(2*h+1) := by
      calc
        _ = 2^(h*2)*2 := by rw [pow_mul]; ring
        _ = 2^(2*h+1) := by rw [pow_add,pow_one,Nat.mul_comm 2 h]
    have ha (i : Fin n) : NativeSignedArithmetic.Bounded (2^(2*h+1)) (normal y i) := by
      rw [←hh]
      exact NativeRationalBounds.subtract (2^h) _ _ (hc.2 _) (hc.2 _)
    exact ⟨(NativeCutResources.guard_bound n (2*h+1) (normal y) ha).trans_le hB,ha⟩
  | infeasible _ => trivial
  | unbounded _ _ => trivial

def command (p : Lax808846.Ram.Program) (coeff : List ℕ) : Com :=
  .seq (NativeProjectionOracle.command p coeff) NativeProjectionCut.command

/-- A single fixed host command constructs and solves the distance LP,
reads its exact certificate, and returns either the nearby point or the
integer normal used by the rounded ellipsoid update. The height guard is
derived from the chosen solver's certified word bound. -/
theorem exists_invocation (f : List ℕ → List ℕ) (hf : RamPolytime f)
    (he : NativeEncodedLP.Encoded f) :
    ∃ (p : Lax808846.Ram.Program) (wp tp : Polynomial ℕ) (coeff : List ℕ),
    (∀ z : ℕ,RamPolynomial.value coeff z=wp.eval z) ∧
    ∀ (m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (ρ : ℚ) (h B : ℕ),
    let query := encodeProgram (distanceProgram P x)
    shapeSize m n<B → Bounded B P x →
      wp.eval (bitSize query)≤h → NativeSignedArithmetic.Bounded (2^h) ρ →
      2*(2^h)^2+3<B → 2^(NativeCutResources.wordExponent n (2*h+1))≤B →
      bitSize query+1<B → wp.eval (bitSize query+1)<B →
      tp.eval (bitSize query)+1<B → RamVirtualConstants.allowance p<B →
      Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧
        Prefix (encodeVector x) "projection.center" σ ∧
        Prefix (encodeRational ρ) "projection.tolerance" σ ∧
        wordLength m n<(σ.arrs "lp.word").length ∧
        3*n≤(σ.arrs "cut.source").length ∧
        query.length<(σ.arrs "vm.input").length ∧
        tp.eval (bitSize query)<(σ.arrs "vm.addresses").length ∧
        tp.eval (bitSize query)<(σ.arrs "vm.values").length ∧
        tp.eval (bitSize query)<(σ.arrs "vm.output").length)
        (command p coeff)
        (fun _ τ => NativeProjectionCut.Output
            (classify P ρ (Lax263307.RegisteredLP.certificate f (distanceProgram P x))) τ ∧
          Prefix (encodeProgram P) "lp.input" τ ∧ Prefix (encodeVector x) "projection.center" τ)
        (NativeDistanceOracle.cost m n p coeff (tp.eval (bitSize query)) (bitSize query)+25+
          NativeProjectionResult.cost (2^h) n+(145*n+38)) := by
  obtain ⟨p,wp,tp,coeff,hcoeff,hfit,hcall⟩ := NativeProjectionOracle.exists_invocation f hf he
  refine ⟨p,wp,tp,coeff,hcoeff,?_⟩
  intro m n P x ρ h B
  dsimp only
  intro hshape hb hheight hρ hB hcut hsize hpoly htime hallow
  have hM : 2^(wp.eval (bitSize (encodeProgram (distanceProgram P x))))≤2^h :=
    Nat.pow_le_pow_right (by decide) hheight
  let c := Lax263307.RegisteredLP.certificate f (distanceProgram P x)
  have hc : NativeProjectionResult.CertificateBounded (2^h) c := by
    apply NativeProjectionOracle.certificate_bound (2^h) m n c
    intro v hv
    have hv' : v∈f (encodeProgram (distanceProgram P x)) := by
      rwa [(he _ _ (distanceProgram P x)).1]
    exact ((hfit m n P x) v hv').le.trans hM
  have hs : m+n+3<B := by
    dsimp [shapeSize,wordLength,rows,columns] at hshape
    omega
  have hlength : 3*n≤wordLength m n := by dsimp [wordLength,rows,columns]; omega
  rintro σ ⟨hp,hx,hρwords,hr,hC,hI,hA,hV,hO⟩
  obtain ⟨ν,r1,p1⟩ := hcall m n P x ρ (2^h) B hshape hb hM hρ hB hsize hpoly htime hallow σ
    ⟨hp,hx,hρwords,hr,hI,hA,hV,hO⟩
  obtain ⟨τ,r2,p2⟩ := NativeProjectionCut.command_spec B (2^(2*h+1)) m n P (classify P ρ c) hs
    (classify_guard B h m n P ρ c hc hcut) ν
    ⟨p1.2.1,p1.1,by rwa [RamFrames.run_array_length r1],
      by rw [RamFrames.run_array_length r1]; exact hlength.trans_lt hr⟩
  refine ⟨τ,r1.seq r2,p2.1,p2.2,?_⟩
  simpa only [Prefix,r2.frame_arr "projection.center" (by decide)] using p1.2.2.1

end Lax263307Proofs.NativeIntegerProjection
