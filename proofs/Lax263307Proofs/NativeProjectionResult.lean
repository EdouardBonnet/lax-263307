import Lax263307Proofs.NativeProjectionDecide
import Lax263307Proofs.NativeProjectionVectors
import Lax263307Proofs.NativeProjectionNear
import Lax263307Proofs.NativeDistanceMetadata

set_option maxRecDepth 10000
set_option maxHeartbeats 400000

namespace Lax263307Proofs.NativeProjectionResult

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.DistanceProjection Lax263307.RationalProjection
open NativeSignedArithmetic

/-- The projected search discards the numerical dual bound, so its native
result stores only the branch tag and the point or separating normal. -/
def Output {n : ℕ} : Outcome n → Env → Prop
  | .near x, σ => σ.vars "projection.kind"=0 ∧ Prefix (encodeVector x) "lp.word" σ ∧ σ.vars "lp.position"=3*n
  | .far a _, σ => σ.vars "projection.kind"=1 ∧ Prefix (encodeVector a) "lp.word" σ ∧ σ.vars "lp.position"=3*n
  | .reject, σ => σ.vars "projection.kind"=2

def CertificateBounded (M : ℕ) {m n : ℕ} : Certificate (m+(n+n)) (n+1) → Prop
  | .optimal z y => (∀ i,Bounded M (z i)) ∧ ∀ i,Bounded M (y i)
  | _ => True

def finish : Com := .ite (.eq (.var "projection.kind") (.lit 0)) NativeProjectionNear.command
  (.ite (.eq (.var "projection.kind") (.lit 1)) NativeProjectionVectors.normalCommand .skip)

def command : Com := .seq NativeDistanceMetadata.readDimensions
  (.seq NativeProjectionDecide.command finish)

def cost (M n : ℕ) : ℕ := (36*(M^2).size+300)*(n+1)+200

theorem finish_reject_spec (B : ℕ) (h2 : 2<B) :
    Spec B (fun σ => σ.vars "projection.kind"=2) finish
      (fun _ τ => τ.vars "projection.kind"=2) 9 := by
  intro σ hh
  have he0 : (Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some false := by
    rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hh.symm,hh ▸ h2⟩)
      (evalB_lit (by omega : 0<B))]
    rfl
  have he1 : (Cond.eq (.var "projection.kind") (.lit 1)).evalB B σ=some false := by
    rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hh.symm,hh ▸ h2⟩)
      (evalB_lit (by omega : 1<B))]
    rfl
  exact ⟨σ,Run.ite_false he0 (Run.ite_false he1 Run.skip),hh⟩

theorem finish_optimal_spec (B M m n : ℕ) (P : Program ℚ m n)
    (z : Fin (n+1) → ℚ) (y : Fin (m+(n+n)) → ℚ) (ρ : ℚ)
    (hB : 2*M^2+3<B) (hs : 3*m+10*n+20<B)
    (hz : ∀ i,Bounded M (z i)) (hy : ∀ i,Bounded M (y i)) :
    Spec B (fun σ => NativeProjectionNormal.Context z y σ ∧
      σ.vars "projection.kind"=NativeProjectionDecide.decision ρ (.optimal z y) ∧
      3*n<(σ.arrs "lp.word").length) finish
      (fun _ τ => Output (classify P ρ (.optimal z y)) τ)
      ((36*(M^2).size+300)*(n+1)+20) := by
  rintro σ ⟨hc,hk,hr⟩
  have hM : M<B := by nlinarith
  have h1 : 1<B := by nlinarith
  by_cases hnear : distance z≤ρ
  · have hk0 : σ.vars "projection.kind"=0 := by simpa only [NativeProjectionDecide.decision,if_pos hnear] using hk
    obtain ⟨τ,rr,ht⟩ := NativeProjectionNear.command_spec B m n z y (by omega)
      (NativeRationalBounds.vector_words B M n (point z) h1 hM (fun i => hz _)) σ
      ⟨hc.1,hc.2.2,hr.le⟩
    have he : (Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some true := by
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hk0.symm,hk0 ▸ (by omega : 0<B)⟩)
        (evalB_lit (by omega : 0<B))]
      rfl
    refine ⟨τ,(Run.ite_true (d := .ite (.eq (.var "projection.kind") (.lit 1)) NativeProjectionVectors.normalCommand .skip) he rr).mono (by dsimp [Cond.size,Expr.size]; nlinarith),?_⟩
    simp only [classify,if_pos hnear,Output]
    exact ⟨(rr.frame_var "projection.kind" (by decide)).trans hk0,ht⟩
  · have hk1 : σ.vars "projection.kind"=1 := by simpa only [NativeProjectionDecide.decision,if_neg hnear] using hk
    obtain ⟨τ,rr,ht⟩ := NativeProjectionVectors.normal_spec B M m n z y hB hs hy σ ⟨hc,hr⟩
    have he0 : (Cond.eq (.var "projection.kind") (.lit 0)).evalB B σ=some false := by
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hk1.symm,hk1 ▸ h1⟩)
        (evalB_lit (by omega : 0<B))]
      rfl
    have he1 : (Cond.eq (.var "projection.kind") (.lit 1)).evalB B σ=some true := by
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨hk1.symm,hk1 ▸ h1⟩) (evalB_lit h1)]
      rfl
    refine ⟨τ,(Run.ite_false (c := NativeProjectionNear.command) he0 (Run.ite_true (d := .skip) he1 rr)).mono (by dsimp [Cond.size,Expr.size]; nlinarith),?_⟩
    simp only [classify,if_neg hnear,Output]
    exact ⟨(rr.frame_var "projection.kind" (by decide)).trans hk1,ht.2⟩

/-- Complete native classification of the registered distance certificate.
The result is exactly the projection result consumed by the computable
round-or-cut search, with its unused dual bound omitted from storage. -/
theorem command_spec (B M m n : ℕ) (P : Program ℚ m n)
    (c : Certificate (m+(n+n)) (n+1)) (ρ : ℚ)
    (hB : 2*M^2+3<B) (hs : 3*m+10*n+20<B)
    (hc : CertificateBounded M c) (hρ : Bounded M ρ) :
    Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧
      Prefix (encodeCertificate c) "vm.output" σ ∧ Stored "projection.tolerance" ρ σ ∧
      3*n<(σ.arrs "lp.word").length) command
      (fun _ τ => Output (classify P ρ c) τ ∧ Prefix (encodeProgram P) "lp.input" τ)
      (cost M n) := by
  rintro σ ⟨hp,hcert,hT,hr⟩
  obtain ⟨ν,r1,p1⟩ := NativeDistanceMetadata.read_dimensions_spec B m n P (by omega) σ hp
  have hcertν : Prefix (encodeCertificate c) "vm.output" ν := by
    simpa only [Prefix,r1.frame_arr "vm.output" (by decide)] using hcert
  have hTν : Stored "projection.tolerance" ρ ν := by
    simpa only [Stored,String.reduceAppend,r1.frame_var "projection.tolerance.s" (by decide),
      r1.frame_var "projection.tolerance.n" (by decide),r1.frame_var "projection.tolerance.d" (by decide)] using hT
  have hdist : NativeProjectionDecide.DistanceBounded M c := by
    cases c with
    | optimal z y => exact hc.1 _
    | infeasible _ => trivial
    | unbounded _ _ => trivial
  obtain ⟨μ,r2,p2⟩ := NativeProjectionDecide.command_spec B M m n c ρ hB (by omega) hρ hdist ν ⟨hcertν,p1.2,hTν⟩
  have hcertμ : Prefix (encodeCertificate c) "vm.output" μ := by
    simpa only [Prefix,r2.frame_arr "vm.output" (by decide)] using hcertν
  have hm := (r2.frame_var "projection.m" (by decide)).trans p1.1
  have hn := (r2.frame_var "projection.n" (by decide)).trans p1.2
  have hroom : 3*n<(μ.arrs "lp.word").length := by rwa [RamFrames.run_array_length (r1.seq r2)]
  cases c with
  | optimal z y =>
    obtain ⟨τ,r3,p3⟩ := finish_optimal_spec B M m n P z y ρ hB hs hc.1 hc.2 μ ⟨⟨hcertμ,hm,hn⟩,p2,hroom⟩
    have rr := r1.seq (r2.seq r3)
    exact ⟨τ,rr.mono (by dsimp [cost]; omega),p3,
      by simpa only [Prefix,rr.frame_arr "lp.input" (by decide)] using hp⟩
  | infeasible y =>
    obtain ⟨τ,r3,p3⟩ := finish_reject_spec B (by omega) μ p2
    have rr := r1.seq (r2.seq r3)
    exact ⟨τ,rr.mono (by dsimp [cost]; omega),p3,
      by simpa only [Prefix,rr.frame_arr "lp.input" (by decide)] using hp⟩
  | unbounded z d =>
    obtain ⟨τ,r3,p3⟩ := finish_reject_spec B (by omega) μ p2
    have rr := r1.seq (r2.seq r3)
    exact ⟨τ,rr.mono (by dsimp [cost]; omega),p3,
      by simpa only [Prefix,rr.frame_arr "lp.input" (by decide)] using hp⟩

end Lax263307Proofs.NativeProjectionResult
