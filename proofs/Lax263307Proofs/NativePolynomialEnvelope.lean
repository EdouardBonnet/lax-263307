import Lax263307Proofs.NativePolynomialBudget

namespace Lax263307Proofs.NativePolynomialEnvelope

/-- A pointwise polynomial bound, used before selecting the single root
monomial. In particular all constants precede the root input. -/
def Bounded (f : ℕ → ℕ) : Prop := ∃ P : Polynomial ℕ,∀ R,f R≤P.eval R

theorem identity : Bounded (fun R => R) := ⟨Polynomial.X,by simp⟩
theorem constant (n : ℕ) : Bounded (fun _ => n) := ⟨Polynomial.C n,by simp⟩

theorem add {f g : ℕ → ℕ} (hf : Bounded f) (hg : Bounded g) : Bounded (fun R => f R+g R) := by
  obtain ⟨P,hP⟩ := hf
  obtain ⟨Q,hQ⟩ := hg
  exact ⟨P+Q,fun R => by simpa only [Polynomial.eval_add] using Nat.add_le_add (hP R) (hQ R)⟩

theorem mul {f g : ℕ → ℕ} (hf : Bounded f) (hg : Bounded g) : Bounded (fun R => f R*g R) := by
  obtain ⟨P,hP⟩ := hf
  obtain ⟨Q,hQ⟩ := hg
  exact ⟨P*Q,fun R => by simpa only [Polynomial.eval_mul] using Nat.mul_le_mul (hP R) (hQ R)⟩

theorem pow {f : ℕ → ℕ} (k : ℕ) (hf : Bounded f) : Bounded (fun R => f R^k) := by
  obtain ⟨P,hP⟩ := hf
  exact ⟨P^k,fun R => by simpa only [Polynomial.eval_pow] using Nat.pow_le_pow_left (hP R) k⟩

theorem eval (P : Polynomial ℕ) {f : ℕ → ℕ} (hf : Bounded f) : Bounded (fun R => P.eval (f R)) := by
  obtain ⟨Q,hQ⟩ := hf
  exact ⟨P.comp Q,fun R => by simpa only [Polynomial.eval_comp] using NativeFlowQueryResources.eval_mono P (hQ R)⟩

theorem of_le {f g : ℕ → ℕ} (hf : Bounded f) (h : ∀ R,g R≤f R) : Bounded g := by
  obtain ⟨P,hP⟩ := hf
  exact ⟨P,fun R => (h R).trans (hP R)⟩

theorem monomial {f : ℕ → ℕ} (hf : Bounded f) :
    ∃ Q e : ℕ,0<Q ∧ 0<e ∧ ∀ R,f R≤Q*(R+1)^e := by
  obtain ⟨P,hP⟩ := hf
  obtain ⟨Q,e,hQ,he,hbound⟩ := NativePolynomialBudget.exists_majorant P
  exact ⟨Q,e,hQ,he,fun R => (hP R).trans (hbound R)⟩

open Lean Meta Elab Tactic

/-- Inspect arithmetic syntax before applying a closure rule. This avoids
unification guessing decompositions of a polynomial-bound existential. -/
private partial def proveEnvelope (goal : MVarId) : MetaM Unit := goal.withContext do
  let target ← goal.getType
  unless target.isAppOf ``Bounded do
    throwError "Expected a polynomial envelope goal"
  let f ← instantiateMVars target.appArg!
  let rule ← withLocalDeclD `R (mkConst ``Nat) fun root => do
    let body := (mkApp f root).headBeta
    if body == root then return ``identity
    if !body.containsFVar root.fvarId! then return ``constant
    let name := body.getAppFn.constName?
    match name with
    | some ``HAdd.hAdd | some ``Nat.add => return ``add
    | some ``HMul.hMul | some ``Nat.mul => return ``mul
    | some ``HPow.hPow | some ``Nat.pow => return ``pow
    | some ``Polynomial.eval => return ``eval
    | _ =>
      let reduced ← whnf body
      if reduced == root then return ``identity
      if !reduced.containsFVar root.fvarId! then return ``constant
      throwError "Unrecognized root arithmetic: {body}"
  let goals ← goal.apply (mkConst rule)
  for next in goals do proveEnvelope next

elab "polynomial_envelope" : tactic => do
  let goal ← getMainGoal
  proveEnvelope goal
  replaceMainGoal []

end Lax263307Proofs.NativePolynomialEnvelope
