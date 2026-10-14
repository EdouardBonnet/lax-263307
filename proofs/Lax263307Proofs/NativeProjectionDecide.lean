import Lax263307Proofs.NativeCertificateRead
import Lax263307Proofs.NativeSignedArithmetic
import Lax263307.RationalProjection

namespace Lax263307Proofs.NativeProjectionDecide

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.DistanceProjection
open NativeSignedArithmetic

def readDistance : Com := .seq (.assign "certificate.index" (.var "projection.n")) NativeCertificateRead.primal

def record : Com := .ite (.eq (.var "cmp.le") (.lit 1))
  (.assign "projection.kind" (.lit 0)) (.assign "projection.kind" (.lit 1))

def optimal : Com := .seq readDistance (.seq (save "left") (.seq (load "projection.tolerance")
  (.seq (save "right") (.seq RamComparison.compareFraction record))))

def reject : Com := .assign "projection.kind" (.lit 2)

def command : Com := .seq NativeCertificateRead.tag
  (.ite (.eq (.var "projection.tag") (.lit 0)) optimal reject)

def decision {m n : ℕ} (ρ : ℚ) : Certificate (m+(n+n)) (n+1) → ℕ
  | .optimal z _ => if distance z≤ρ then 0 else 1
  | _ => 2

theorem readDistance_spec (B m n : ℕ) (z : Fin (n+1) → ℚ) (y : Fin (m+(n+n)) → ℚ)
    (hs : 3*n+10<B) (hn : (distance z).num.natAbs<B) (hd : (distance z).den<B) :
    Spec B (fun σ => Prefix (encodeCertificate (.optimal z y)) "vm.output" σ ∧ σ.vars "projection.n"=n)
      readDistance (fun _ τ => RamRational.FractionOutput (distance z) τ) 25 := by
  rintro σ ⟨hp,hN⟩
  let i : Fin (n+1) := Fin.natAdd n (0 : Fin 1)
  have hv : i.val=n := by simp [i]
  have r1 : Run B (.assign "certificate.index" (.var "projection.n")) σ
      (σ.setVar "certificate.index" n) 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hN.symm,hN ▸ (by omega : n<B)⟩)
  obtain ⟨τ,r2,p2⟩ := NativeCertificateRead.primal_spec B m n z y i hs hn hd
    (σ.setVar "certificate.index" n) ⟨hp,by simp [hv]⟩
  exact ⟨τ,r1.seq r2,p2⟩

theorem record_spec (B : ℕ) (a b : ℚ) (h1 : 1<B) :
    Spec B (fun σ => σ.vars "cmp.le"=if a≤b then 1 else 0) record
      (fun _ τ => τ.vars "projection.kind"=if a≤b then 0 else 1) 6 := by
  have hflagB : (if a≤b then 1 else 0 : ℕ)<B := by split_ifs <;> omega
  by_cases hh : a≤b
  · run_vcg
    all_goals simp_all
  · run_vcg
    all_goals simp_all

theorem optimal_spec (B M m n : ℕ) (z : Fin (n+1) → ℚ) (y : Fin (m+(n+n)) → ℚ) (ρ : ℚ)
    (hB : 2*M^2+3<B) (hs : 3*n+10<B) (hz : Bounded M (distance z)) (hρ : Bounded M ρ) :
    Spec B (fun σ => Prefix (encodeCertificate (.optimal z y)) "vm.output" σ ∧
      σ.vars "projection.n"=n ∧ Stored "projection.tolerance" ρ σ) optimal
      (fun _ τ => τ.vars "projection.kind"=if distance z≤ρ then 0 else 1) 89 := by
  rintro σ ⟨hc,hN,hT⟩
  have h1 : 1<B := by nlinarith
  have hM : M<B := by nlinarith
  obtain ⟨σ1,r1,p1⟩ := readDistance_spec B m n z y hs (hz.1.trans_lt hM) (hz.2.trans_lt hM) σ ⟨hc,hN⟩
  obtain ⟨σ2,r2,p2⟩ := save_spec B "left" (distance z) h1 (hz.1.trans_lt hM) (hz.2.trans_lt hM) (by decide) σ1 p1
  have hT2 : Stored "projection.tolerance" ρ σ2 := by
    simpa only [Stored,String.reduceAppend,(r1.seq r2).frame_var "projection.tolerance.s" (by decide),
      (r1.seq r2).frame_var "projection.tolerance.n" (by decide),
      (r1.seq r2).frame_var "projection.tolerance.d" (by decide)] using hT
  obtain ⟨σ3,r3,p3⟩ := load_spec B "projection.tolerance" ρ h1 (hρ.1.trans_lt hM) (hρ.2.trans_lt hM) (by decide) σ2 hT2
  obtain ⟨σ4,r4,p4⟩ := save_spec B "right" ρ h1 (hρ.1.trans_lt hM) (hρ.2.trans_lt hM) (by decide) σ3 p3
  have hL4 : Stored "left" (distance z) σ4 := by
    simpa only [Stored,String.reduceAppend,(r3.seq r4).frame_var "left.s" (by decide),
      (r3.seq r4).frame_var "left.n" (by decide),(r3.seq r4).frame_var "left.d" (by decide)] using p2
  obtain ⟨σ5,r5,p5⟩ := compare_spec B M (distance z) ρ hB hz hρ σ4 ⟨hL4,p4⟩
  obtain ⟨τ,r6,p6⟩ := record_spec B (distance z) ρ h1 σ5 p5
  exact ⟨τ,r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6)))),p6⟩

def DistanceBounded (M : ℕ) {m n : ℕ} : Certificate (m+(n+n)) (n+1) → Prop
  | .optimal z _ => Bounded M (distance z)
  | _ => True

theorem command_spec (B M m n : ℕ) (c : Certificate (m+(n+n)) (n+1)) (ρ : ℚ)
    (hB : 2*M^2+3<B) (hs : 3*n+10<B) (hρ : Bounded M ρ)
    (hc : DistanceBounded M c) :
    Spec B (fun σ => Prefix (encodeCertificate c) "vm.output" σ ∧
      σ.vars "projection.n"=n ∧ Stored "projection.tolerance" ρ σ) command
      (fun _ τ => τ.vars "projection.kind"=decision ρ c) 96 := by
  rintro σ ⟨hp,hN,hT⟩
  have h3 : 3<B := by omega
  obtain ⟨ν,r1,p1⟩ := NativeCertificateRead.tag_spec B c h3 σ hp
  have hpν : Prefix (encodeCertificate c) "vm.output" ν := by
    simpa only [Prefix,r1.frame_arr "vm.output" (by decide)] using hp
  have hNν := (r1.frame_var "projection.n" (by decide)).trans hN
  have hTν : Stored "projection.tolerance" ρ ν := by
    simpa only [Stored,String.reduceAppend,r1.frame_var "projection.tolerance.s" (by decide),
      r1.frame_var "projection.tolerance.n" (by decide),
      r1.frame_var "projection.tolerance.d" (by decide)] using hT
  cases c with
  | optimal z y =>
    obtain ⟨τ,r2,p2⟩ := optimal_spec B M m n z y ρ hB hs hc hρ ν ⟨hpν,hNν,hTν⟩
    have he : (Cond.eq (.var "projection.tag") (.lit 0)).evalB B ν=some true := by
      simp only [NativeCertificateRead.tagValue] at p1
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ (by omega : 0<B)⟩)
        (evalB_lit (by omega : 0<B))]
      rfl
    exact ⟨τ,(r1.seq (Run.ite_true (d := reject) he r2)).mono (by decide),p2⟩
  | infeasible y =>
    have he : (Cond.eq (.var "projection.tag") (.lit 0)).evalB B ν=some false := by
      simp only [NativeCertificateRead.tagValue] at p1
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ (by omega : 1<B)⟩)
        (evalB_lit (by omega : 0<B))]
      rfl
    have r2 : Run B reject ν (ν.setVar "projection.kind" 2) 2 := Run.assign (evalB_lit (by omega))
    exact ⟨_,(r1.seq (Run.ite_false (c := optimal) he r2)).mono (by decide),by simp [decision]⟩
  | unbounded z d =>
    have he : (Cond.eq (.var "projection.tag") (.lit 0)).evalB B ν=some false := by
      simp only [NativeCertificateRead.tagValue] at p1
      rw [evalB_condEq (by rw [evalB_var_iff]; exact ⟨p1.symm,p1 ▸ (by omega : 2<B)⟩)
        (evalB_lit (by omega : 0<B))]
      rfl
    have r2 : Run B reject ν (ν.setVar "projection.kind" 2) 2 := Run.assign (evalB_lit (by omega))
    exact ⟨_,(r1.seq (Run.ite_false (c := optimal) he r2)).mono (by decide),by simp [decision]⟩

end Lax263307Proofs.NativeProjectionDecide
