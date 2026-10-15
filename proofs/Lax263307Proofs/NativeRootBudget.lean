import Lax263307Proofs.NativeRootResource
import Lax263307Proofs.NativeLogarithms
import Lax263307Proofs.NativeNaturalPower

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRootBudget

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters
open NativeRootResource

def guard (C d Q e n D : ℕ) : ℕ :=
  let X := D*logarithm n
  let H := C*X^d
  let R := envelope C d n D
  let W := budget Q e C d n D
  C+d+Q+e+2*n+D+logarithm n+X+X^d+H+R+(R+1)^e+W+2*(W+1)+100

def first (d : ℕ) : Com := .seq (.assign "power.base" (.mul (.var "node.D") (.var "node.logarithm")))
  (.assign "power.exponent" (.lit d))

def second (C : ℕ) : Com := .seq (.assign "root.exponent" (.mul (.lit C) (.var "power.value")))
  (.seq (.assign "power.base" (.lit 2)) (.assign "power.exponent" (.var "root.exponent")))

def third (e : ℕ) : Com := .seq (.assign "algorithm.resource" (.var "power.value"))
  (.seq (.assign "power.base" (.add (.var "power.value") (.lit 1))) (.assign "power.exponent" (.lit e)))

def finish (Q : ℕ) : Com := .seq (.assign "algorithm.roundWidth" (.mul (.lit Q) (.var "power.value")))
  (.assign "recursion.stride" (.mul (.lit 2) (.add (.var "algorithm.roundWidth") (.lit 1))))

theorem first_spec (B d D L : ℕ) (hB : d+D+L+D*L+3<B) :
    Spec B (fun σ => σ.vars "node.D"=D ∧ σ.vars "node.logarithm"=L) (first d)
      (fun _ τ => NativeNaturalPower.Context (D*L) d τ) 6 := by
  intro σ hs
  run_vcg
  all_goals simp_all [NativeNaturalPower.Context,Env.setVar]
  all_goals omega

theorem second_spec (B C V : ℕ) (hB : C+V+C*V+3<B) :
    Spec B (fun σ => σ.vars "power.value"=V) (second C)
      (fun _ τ => NativeNaturalPower.Context 2 (C*V) τ ∧ τ.vars "root.exponent"=C*V) 8 := by
  intro σ hs
  run_vcg
  all_goals simp_all [NativeNaturalPower.Context,Env.setVar]
  all_goals omega

theorem third_spec (B e R : ℕ) (hB : e+R+3<B) :
    Spec B (fun σ => σ.vars "power.value"=R) (third e)
      (fun _ τ => NativeNaturalPower.Context (R+1) e τ ∧ τ.vars "algorithm.resource"=R) 8 := by
  intro σ hs
  run_vcg
  all_goals simp_all [NativeNaturalPower.Context,Env.setVar]
  all_goals omega

theorem finish_spec (B Q V : ℕ) (hB : Q+V+Q*V+2*(Q*V+1)+3<B) :
    Spec B (fun σ => σ.vars "power.value"=V) (finish Q)
      (fun _ τ => τ.vars "algorithm.roundWidth"=Q*V ∧ τ.vars "recursion.stride"=2*(Q*V+1)) 10 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

def command (C d Q e : ℕ) : Com := .seq NativeLogarithms.command
  (.seq (first d) (.seq NativeNaturalPower.command (.seq (second C)
    (.seq NativeNaturalPower.command (.seq (third e) (.seq NativeNaturalPower.command (finish Q)))))))

/-- Compute the root envelope and actual workspace/rounded-update width
from the root graph and its accuracy denominator. No resource bound is
supplied as an input word or as advice. -/
theorem command_spec (B C d Q e n D : ℕ) (hn : 0<n) (hD : 0<D)
    (hB : guard C d Q e n D<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "node.D"=D) (command C d Q e)
      (fun _ τ => τ.vars "graph.n"=n ∧ τ.vars "node.D"=D ∧
        τ.vars "algorithm.resource"=envelope C d n D ∧
        τ.vars "algorithm.roundWidth"=budget Q e C d n D ∧
        τ.vars "recursion.stride"=2*(budget Q e C d n D+1))
      (12*n.size+12*(2*n).size+12*d+12*(C*(D*logarithm n)^d)+12*e+78) := by
  let X := D*logarithm n
  let H := C*X^d
  let R := envelope C d n D
  have hX : 1≤X := by
    have hp : 0<X := by dsimp [X,logarithm]; positivity
    omega
  have hg := hB
  dsimp only [guard,budget] at hg
  rintro σ ⟨horder,hden⟩
  obtain ⟨σ₁,r0,p0⟩ := NativeLogarithms.command_spec B n hn (by omega) σ horder
  obtain ⟨σ₂,r1,p1⟩ := first_spec B d D (logarithm n) (by omega) σ₁
    ⟨(r0.frame_var _ (by decide)).trans hden,p0.2.2⟩
  obtain ⟨σ₃,r2,p2⟩ := NativeNaturalPower.command_spec B X d hX (by dsimp [X]; omega) σ₂ p1
  obtain ⟨σ₄,r3,p3⟩ := second_spec B C (X^d) (by dsimp [X]; omega) σ₃ p2.2
  obtain ⟨σ₅,r4,p4⟩ := NativeNaturalPower.command_spec B 2 H (by decide) (by
    change 2+H+R+3<B
    dsimp only [H,R,X]
    omega) σ₄ p3.1
  obtain ⟨σ₆,r5,p5⟩ := third_spec B e R (by dsimp [R]; omega) σ₅ p4.2
  obtain ⟨σ₇,r6,p6⟩ := NativeNaturalPower.command_spec B (R+1) e (by omega) (by dsimp [R]; omega) σ₆ p5.1
  obtain ⟨τ,r7,p7⟩ := finish_spec B Q ((R+1)^e) (by dsimp [R]; omega) σ₇ p6.2
  have rr := r0.seq (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7))))))
  refine ⟨τ,rr.mono (by dsimp only [H,X]; omega),?_,?_,?_,p7⟩
  · exact (rr.frame_var "graph.n" (by
      change "graph.n"∉(command 0 0 0 0).wvars
      decide)).trans horder
  · exact (rr.frame_var "node.D" (by
      change "node.D"∉(command 0 0 0 0).wvars
      decide)).trans hden
  · exact ((r6.seq r7).frame_var "algorithm.resource" (by
      simp [NativeNaturalPower.command,NativeNaturalPower.step,finish,Com.wvars])).trans p5.2


end Lax263307Proofs.NativeRootBudget
