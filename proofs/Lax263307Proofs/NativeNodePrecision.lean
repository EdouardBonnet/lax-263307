import Lax263307Proofs.NativeNodeParameters

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodePrecision

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 AlgorithmParameters

def radius (n D N b r : ℕ) : ℕ := 256*N*n*n*D*D*b^r
def prec (n D N b r : ℕ) : ℕ := radius n D N b r+2
def count (n D N b r : ℕ) : ℕ := 4*(N+1)*(prec n D N b r*N+1)
def guard (n D N b r : ℕ) : ℕ :=
  256+n+D+N+b+r+b^r+256*N+256*N*n+256*N*n*n+256*N*n*n*D+
    256*N*n*n*D*D+radius n D N b r+prec n D N b r+(N+1)+prec n D N b r*N+
    (prec n D N b r*N+1)+4*(N+1)+count n D N b r+20

def Context (n D N b r : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "node.D"=D ∧ σ.vars "catalog.count"=N ∧
    σ.vars "node.floorDen"=b ∧ σ.vars "moment.r"=r

def Output (n D N b r : ℕ) (σ : Env) : Prop := Context n D N b r σ ∧
  σ.vars "node.floorPower"=b^r ∧ σ.vars "node.radius"=radius n D N b r ∧
  σ.vars "node.precision"=prec n D N b r ∧ σ.vars "round.limit"=count n D N b r ∧
  σ.vars "vec.n"=N

def setup : Com := .seq (.assign "power.base" (.var "node.floorDen"))
  (.assign "power.exponent" (.var "moment.r"))

def saveRadius : Com := .seq (.assign "node.floorPower" (.var "power.value"))
  (.assign "node.radius" (.mul (.mul (.mul (.mul (.mul (.mul (.lit 256) (.var "catalog.count"))
    (.var "graph.n")) (.var "graph.n")) (.var "node.D")) (.var "node.D")) (.var "power.value")))

def saveBudgets : Com := .seq (.assign "node.precision" (.add (.var "node.radius") (.lit 2)))
  (.seq (.assign "round.limit" (.mul (.mul (.lit 4) (.add (.var "catalog.count") (.lit 1)))
    (.add (.mul (.var "node.precision") (.var "catalog.count")) (.lit 1))))
    (.assign "vec.n" (.var "catalog.count")))

def command : Com := .seq setup (.seq NativeNaturalPower.command (.seq saveRadius saveBudgets))

theorem context_frame {B n D N b r t : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ t)
    (hs : Context n D N b r σ) (hn : "graph.n"∉c.wvars) (hD : "node.D"∉c.wvars)
    (hN : "catalog.count"∉c.wvars) (hb : "node.floorDen"∉c.wvars) (hr : "moment.r"∉c.wvars) :
    Context n D N b r τ :=
  ⟨(rr.frame_var _ hn).trans hs.1,(rr.frame_var _ hD).trans hs.2.1,
    (rr.frame_var _ hN).trans hs.2.2.1,(rr.frame_var _ hb).trans hs.2.2.2.1,
    (rr.frame_var _ hr).trans hs.2.2.2.2⟩

theorem setup_spec (B n D N b r : ℕ) (hB : guard n D N b r<B) :
    Spec B (Context n D N b r) setup
      (fun _ τ => Context n D N b r τ ∧ NativeNaturalPower.Context b r τ) 4 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Context,NativeNaturalPower.Context,guard,Env.setVar]
  all_goals omega

theorem radius_spec (B n D N b r : ℕ) (hB : guard n D N b r<B) :
    Spec B (fun σ => Context n D N b r σ ∧ σ.vars "power.value"=b^r) saveRadius
      (fun _ τ => Context n D N b r τ ∧ τ.vars "node.floorPower"=b^r ∧
        τ.vars "node.radius"=radius n D N b r) 16 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Context,guard,radius,Env.setVar]
  all_goals omega

theorem budgets_spec (B n D N b r : ℕ) (hB : guard n D N b r<B) :
    Spec B (fun σ => Context n D N b r σ ∧ σ.vars "node.floorPower"=b^r ∧
      σ.vars "node.radius"=radius n D N b r) saveBudgets
      (fun _ τ => Output n D N b r τ) 18 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Context,Output,guard,prec,count,Env.setVar]
  all_goals omega

/-- Compute the protected-radius precision and the actual numeric
rounded-search iteration budget from the current node's stored data. -/
theorem command_spec (B n D N b r : ℕ) (hb : 1≤b) (hB : guard n D N b r<B) :
    Spec B (Context n D N b r) command
      (fun _ τ => Output n D N b r τ) (12*r+46) := by
  intro σ hs
  obtain ⟨ν,r1,p1⟩ := setup_spec B n D N b r hB σ hs
  obtain ⟨μ,r2,p2⟩ := NativeNaturalPower.command_spec B b r hb
    (by dsimp only [guard] at hB; omega) ν p1.2
  have hd2 := context_frame r2 p1.1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨ρ,r3,p3⟩ := radius_spec B n D N b r hB μ ⟨hd2,p2.2⟩
  obtain ⟨τ,r4,p4⟩ := budgets_spec B n D N b r hB ρ p3
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),p4⟩

theorem actual_radius (a K b n D : ℕ) :
    radius n D (MomentLP.dimension n (level a K b n D))
      (floorDenominator a K b n D) (level a K b n D)=radiusDenominator a K b n D := by
  unfold radius radiusDenominator
  ring

theorem actual_precision (a K b n D : ℕ) :
    prec n D (MomentLP.dimension n (level a K b n D))
      (floorDenominator a K b n D) (level a K b n D)=precision a K b n D := by
  rw [prec,actual_radius]
  rfl

theorem actual_iterations (a K b n D : ℕ) :
    count n D (MomentLP.dimension n (level a K b n D))
      (floorDenominator a K b n D) (level a K b n D)=iterations a K b n D := by
  rw [count,actual_precision]
  rfl

end Lax263307Proofs.NativeNodePrecision
