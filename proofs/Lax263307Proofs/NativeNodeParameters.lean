import Lax263307Proofs.NativeLogarithms
import Lax263307Proofs.NativeNaturalPower
import Lax263307Proofs.ParameterResources

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodeParameters

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307.AlgorithmParameters

def guard (a K b n D : ℕ) : ℕ :=
  a+K+12*b+n+D+2*n+(Nat.log2 n+1)+logarithm n+12*b*D+load b n D+
    (load b n D+1)+(4*a+2)+(load b n D+1)^(4*a+2)+targetThreshold a K b n D+
    sparsity a K b n D+level a K b n D+floorDenominator a K b n D+20

def Context (n D : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "node.D"=D ∧ σ.vars "node.log"=Nat.log2 n+1 ∧
    σ.vars "node.logarithm"=logarithm n

def Data (a K b n D : ℕ) (σ : Env) : Prop := Context n D σ ∧
  σ.vars "node.load"=load b n D ∧ σ.vars "node.threshold"=targetThreshold a K b n D ∧
  σ.vars "node.sparsity"=sparsity a K b n D ∧ σ.vars "moment.r"=level a K b n D ∧
  σ.vars "node.cutoff"=cutoff a K b n D ∧ σ.vars "node.floorDen"=floorDenominator a K b n D

def setup (a b : ℕ) : Com :=
  .seq (.assign "node.load" (.mul (.mul (.lit (12*b)) (.var "node.D")) (.var "node.logarithm")))
    (.seq (.assign "power.base" (.add (.var "node.load") (.lit 1)))
      (.assign "power.exponent" (.lit (4*a+2))))

def finish (K : ℕ) : Com :=
  .seq (.assign "node.threshold" (.mul (.lit K) (.var "power.value")))
    (.seq (.assign "node.sparsity" (.mul (.lit 2) (.var "node.threshold")))
      (.seq (.assign "node.level" (.mul (.var "node.sparsity") (.var "node.log")))
        (.seq (.assign "node.cutoff" (.var "node.level"))
          (.seq (.assign "moment.r" (.var "node.level"))
            (.assign "node.floorDen" (.mul (.mul (.lit 2) (.var "graph.n")) (.var "node.level")))))))

def command (a K b : ℕ) : Com := .seq NativeLogarithms.command
  (.seq (setup a b) (.seq NativeNaturalPower.command (finish K)))

theorem context_frame {B n D t : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ t)
    (hs : Context n D σ) (hn : "graph.n"∉c.wvars) (hD : "node.D"∉c.wvars)
    (hl : "node.log"∉c.wvars) (hL : "node.logarithm"∉c.wvars) : Context n D τ :=
  ⟨(rr.frame_var _ hn).trans hs.1,(rr.frame_var _ hD).trans hs.2.1,
    (rr.frame_var _ hl).trans hs.2.2.1,(rr.frame_var _ hL).trans hs.2.2.2⟩

theorem floor_eq (a K b n D : ℕ) : floorDenominator a K b n D=2*n*level a K b n D := by
  unfold floorDenominator level
  ring

theorem setup_spec (B a K b n D : ℕ) (hB : guard a K b n D<B) :
    Spec B (Context n D) (setup a b)
      (fun _ τ => Context n D τ ∧ τ.vars "node.load"=load b n D ∧
        NativeNaturalPower.Context (load b n D+1) (4*a+2) τ) 12 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Context,NativeNaturalPower.Context,Env.setVar,guard,load]
  all_goals omega

theorem finish_spec (B a K b n D : ℕ) (hB : guard a K b n D<B) :
    Spec B (fun σ => Context n D σ ∧ σ.vars "node.load"=load b n D ∧
      σ.vars "power.value"=(load b n D+1)^(4*a+2)) (finish K)
      (fun _ τ => Data a K b n D τ) 22 := by
  have hg := hB
  dsimp only [guard] at hg
  have hth : K*(load b n D+1)^(4*a+2)=targetThreshold a K b n D := rfl
  have hsp : 2*targetThreshold a K b n D=sparsity a K b n D := rfl
  have hl : sparsity a K b n D*(Nat.log2 n+1)=level a K b n D := rfl
  have hf := floor_eq a K b n D
  rintro σ ⟨hc,hload,hpower⟩
  let ν := σ.setVar "node.threshold" (targetThreshold a K b n D)
  have r1 : Run B (.assign "node.threshold" (.mul (.lit K) (.var "power.value"))) σ ν 4 := Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show K<B by omega))
      (by rw [evalB_var_iff]; exact ⟨hpower.symm,hpower ▸ (by omega)⟩)
      (by change K*(load b n D+1)^(4*a+2)<B; rw [hth]; omega))
  have hν : ν.vars "node.threshold"=targetThreshold a K b n D := by rfl
  let μ := ν.setVar "node.sparsity" (sparsity a K b n D)
  have r2 : Run B (.assign "node.sparsity" (.mul (.lit 2) (.var "node.threshold"))) ν μ 4 := Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show 2<B by omega))
      (by rw [evalB_var_iff]; exact ⟨hν.symm,hν ▸ (by omega)⟩)
      (by change 2*targetThreshold a K b n D<B; rw [hsp]; omega))
  have hμ : μ.vars "node.sparsity"=sparsity a K b n D := by rfl
  have hlog := ((r1.seq r2).frame_var "node.log" (by simp [Com.wvars])).trans hc.2.2.1
  let ρ := μ.setVar "node.level" (level a K b n D)
  have r3 : Run B (.assign "node.level" (.mul (.var "node.sparsity") (.var "node.log"))) μ ρ 4 := Run.assign
    (evalB_bin (op:=.mul)
      (by rw [evalB_var_iff]; exact ⟨hμ.symm,hμ ▸ (by omega)⟩)
      (by rw [evalB_var_iff]; exact ⟨hlog.symm,hlog ▸ (by omega)⟩)
      (by change sparsity a K b n D*(Nat.log2 n+1)<B; rw [hl]; omega))
  have hρ : ρ.vars "node.level"=level a K b n D := by rfl
  let υ := ρ.setVar "node.cutoff" (level a K b n D)
  have r4 : Run B (.assign "node.cutoff" (.var "node.level")) ρ υ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hρ.symm,hρ ▸ (by omega)⟩)
  have hυ := (r4.frame_var "node.level" (by simp [Com.wvars])).trans hρ
  let τ := υ.setVar "moment.r" (level a K b n D)
  have r5 : Run B (.assign "moment.r" (.var "node.level")) υ τ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hυ.symm,hυ ▸ (by omega)⟩)
  have hτ := (r5.frame_var "node.level" (by simp [Com.wvars])).trans hυ
  have horder := ((r1.seq (r2.seq (r3.seq (r4.seq r5)))).frame_var "graph.n" (by simp [Com.wvars])).trans hc.1
  let κ := τ.setVar "node.floorDen" (floorDenominator a K b n D)
  have r6 : Run B (.assign "node.floorDen" (.mul (.mul (.lit 2) (.var "graph.n")) (.var "node.level"))) τ κ 6 := by
    apply Run.assign
    rw [hf]
    apply evalB_bin (op:=.mul)
    · exact evalB_bin (op:=.mul) (evalB_lit (show 2<B by omega))
        (by rw [evalB_var_iff]; exact ⟨horder.symm,horder ▸ (by omega)⟩) (by change 2*n<B; omega)
    · rw [evalB_var_iff]; exact ⟨hτ.symm,hτ ▸ (by omega)⟩
    · change 2*n*level a K b n D<B
      rw [←hf]
      omega
  have rr := r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))
  refine ⟨κ,rr,⟨context_frame rr hc (by simp [Com.wvars]) (by simp [Com.wvars]) (by simp [Com.wvars]) (by simp [Com.wvars]),
    (rr.frame_var "node.load" (by simp [Com.wvars])).trans hload,
    ((r2.seq (r3.seq (r4.seq (r5.seq r6)))).frame_var "node.threshold" (by simp [Com.wvars])).trans hν,
    ((r3.seq (r4.seq (r5.seq r6))).frame_var "node.sparsity" (by simp [Com.wvars])).trans hμ,
    (r6.frame_var "moment.r" (by simp [Com.wvars])).trans (by rfl),?_,by rfl⟩⟩
  rw [Lax263307Proofs.ParameterResources.cutoff_eq_level]
  exact ((r5.seq r6).frame_var "node.cutoff" (by simp [Com.wvars])).trans (by rfl)

/-- Compute the actual graph/accuracy-dependent combinatorial budgets
using fixed class literals, native logarithms and a multiplication loop. -/
theorem command_spec (B a K b n D : ℕ) (hn : 0<n) (hB : guard a K b n D<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "node.D"=D) (command a K b)
      (fun _ τ => Data a K b n D τ) (12*n.size+12*(2*n).size+12*(4*a+2)+64) := by
  rintro σ ⟨hnσ,hDσ⟩
  obtain ⟨ν,r1,p1⟩ := NativeLogarithms.command_spec B n hn (by dsimp [guard] at hB; omega) σ hnσ
  have hd1 : Context n D ν := ⟨p1.1,(r1.frame_var "node.D" (by decide)).trans hDσ,p1.2⟩
  obtain ⟨μ,r2,p2⟩ := setup_spec B a K b n D hB ν hd1
  obtain ⟨ρ,r3,p3⟩ := NativeNaturalPower.command_spec B (load b n D+1) (4*a+2) (by omega)
    (by dsimp [guard] at hB; omega) μ p2.2.2
  have hd3 := context_frame r3 p2.1 (by decide) (by decide) (by decide) (by decide)
  have hl3 := (r3.frame_var "node.load" (by decide)).trans p2.2.1
  obtain ⟨τ,r4,p4⟩ := finish_spec B a K b n D hB ρ ⟨hd3,hl3,p3.2⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),p4⟩

end Lax263307Proofs.NativeNodeParameters
