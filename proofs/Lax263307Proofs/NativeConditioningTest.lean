import Lax263307Proofs.NativeConditioningPredicate

set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeConditioningTest

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational NativeSignedArithmetic NativeConditioningPredicate

/-- Include every intermediate unsigned product in the overflow guard. -/
def resource (k p D n d m e : ℕ) : ℕ := p+k+D+n+d+m+e+3+
  p*m+p*m*d+p*m*d*d+2*k+2*k*k+2*k*k*n+2*k*k*n*n+2*k*k*n*n*e+D*n

def Input (k p D s n d t m e : ℕ) (σ : Env) : Prop :=
  σ.vars "conditioning.k"=k ∧ σ.vars "conditioning.p"=p ∧ σ.vars "conditioning.floorDen"=D ∧
  σ.vars "conditioning.a.s"=s ∧ σ.vars "conditioning.a.n"=n ∧ σ.vars "conditioning.a.d"=d ∧
  σ.vars "conditioning.edge.s"=t ∧ σ.vars "conditioning.edge.n"=m ∧ σ.vars "conditioning.edge.d"=e

def products : Com := .seq
  (.assign "conditioning.left" (.mul (.mul (.mul (.var "conditioning.p") (.var "conditioning.edge.n"))
    (.var "conditioning.a.d")) (.var "conditioning.a.d")))
  (.seq (.assign "conditioning.right" (.mul (.mul (.mul (.mul (.mul (.lit 2) (.var "conditioning.k"))
    (.var "conditioning.k")) (.var "conditioning.a.n")) (.var "conditioning.a.n")) (.var "conditioning.edge.d")))
    (.assign "conditioning.floorProduct" (.mul (.var "conditioning.floorDen") (.var "conditioning.a.n"))))

def answer (b : ℕ) : Com := .assign "conditioning.passes" (.lit b)

def decideCommand : Com := .ite (.eq (.var "conditioning.a.s") (.lit 0))
  (.ite (.lt (.lit 0) (.var "conditioning.a.n"))
    (.ite (.lt (.var "conditioning.floorProduct") (.var "conditioning.a.d")) (answer 0)
      (.ite (.eq (.var "conditioning.edge.s") (.lit 1)) (answer 1)
        (.ite (.lt (.var "conditioning.right") (.var "conditioning.left")) (answer 0) (answer 1))))
    (answer 0)) (answer 0)

def command : Com := .seq products decideCommand

theorem command_spec (B k p D s n d t m e : ℕ) (hs : s≤1) (ht : t≤1)
    (hB : resource k p D n d m e<B) :
    Spec B (Input k p D s n d t m e) command
      (fun _ τ => τ.vars "conditioning.passes"=if Numeric k p D s n d t m e then 1 else 0) 46 := by
  dsimp [resource] at hB
  run_vcg
  all_goals simp_all [Input,Numeric]
  all_goals first | omega | (split_ifs at * <;> omega)

/-- Test the positivity, edge-cost and moment-floor conditions on the
actual stored rationals, using exact unsigned cross products. -/
theorem stored_spec (B k p D : ℕ) (q e : ℚ) (hD : 0<D)
    (hB : resource k p D q.num.natAbs q.den e.num.natAbs e.den<B) :
    Spec B (fun σ => σ.vars "conditioning.k"=k ∧ σ.vars "conditioning.p"=p ∧
      σ.vars "conditioning.floorDen"=D ∧ Stored "conditioning.a" q σ ∧ Stored "conditioning.edge" e σ)
      command (fun _ τ => τ.vars "conditioning.passes"=if Test k p D q e then 1 else 0) 46 := by
  rintro σ ⟨hk,hp,hd,hq,he⟩
  have hq' := hq
  have he' := he
  simp only [Stored,String.reduceAppend] at hq' he'
  obtain ⟨τ,rr,ht⟩ := command_spec B k p D (σ.vars "conditioning.a.s") q.num.natAbs q.den
    (σ.vars "conditioning.edge.s") e.num.natAbs e.den hq'.2.2.2 he'.2.2.2 hB σ
    ⟨hk,hp,hd,rfl,hq'.2.1,hq'.2.2.1,rfl,he'.2.1,he'.2.2.1⟩
  have hi := numeric_iff k p D (σ.vars "conditioning.a.s") q.num.natAbs q.den
    (σ.vars "conditioning.edge.s") e.num.natAbs e.den hq'.2.2.2 he'.2.2.2 q.den_pos e.den_pos hD
  have hvq : fractionValue (σ.vars "conditioning.a.s") q.num.natAbs q.den=q := by
    simpa only [←hq'.2.1,←hq'.2.2.1] using hq'.1
  have hve : fractionValue (σ.vars "conditioning.edge.s") e.num.natAbs e.den=e := by
    simpa only [←he'.2.1,←he'.2.2.1] using he'.1
  rw [hvq,hve] at hi
  exact ⟨τ,rr,by simpa only [hi] using ht⟩

end Lax263307Proofs.NativeConditioningTest
