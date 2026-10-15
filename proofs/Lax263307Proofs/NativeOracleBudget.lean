import Lax263307Proofs.NativeFlowBudget

namespace Lax263307Proofs.NativeOracleBudget

open Lax455465Proofs

private theorem monomial_sum (Q₁ Q₂ e₁ e₂ R : ℕ) :
    Q₁*(R+1)^e₁+Q₂*(R+1)^e₂≤(Q₁+Q₂)*(R+1)^(max e₁ e₂) := by
  have h₁ := Nat.pow_le_pow_right (by omega : 1≤R+1) (Nat.le_max_left e₁ e₂)
  have h₂ := Nat.pow_le_pow_right (by omega : 1≤R+1) (Nat.le_max_right e₁ e₂)
  calc
    _≤Q₁*(R+1)^(max e₁ e₂)+Q₂*(R+1)^(max e₁ e₂) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ h₁) (Nat.mul_le_mul_left _ h₂)
    _=_ := by ring

/-- The selected LP and flow programs and the rounded program have one
common root monomial covering query storage, certified cut height, virtual
word widths, oracle workspaces and the complete native separator time.
The constants depend only on fixed programs and polynomials. -/
theorem exists_budget (b c allowance : ℕ) (lpWidth lpTime flowWidth flowTime flowOutput : Polynomial ℕ)
    (flowProgram : Lax808846.Ram.Program) (flowCoeff : List ℕ) :
    ∃ Q e : ℕ,0<Q ∧ 0<e ∧ ∀ n load k h R,n≤R → load≤R → k≤R →
      h≤(NativePolynomialBudget.heightPolynomial lpWidth).eval R →
      let H := NativeLargeResources.heightExponent b n load k h
      1000000*(R+1)^6+NativeOraclePrecision.roundedHeight lpWidth R+
        c*(2*R+NativeOraclePrecision.roundedHeight lpWidth R+1)^12+1+
        lpWidth.eval (1000000*(R+1)^6+1)+lpTime.eval (1000000*(R+1)^6)+allowance+1+
        NativeUniformFlow.wordHeight n H flowProgram flowWidth flowTime flowOutput+
        NativeUniformFlow.spaceBound n H flowTime+
        NativeSeparatorOutput.timeBound n H flowProgram flowCoeff flowTime≤Q*(R+1)^e := by
  obtain ⟨Qr,er,hQr,her,hr⟩ := NativePolynomialBudget.exists_rounded_budget lpWidth c
  obtain ⟨Qf,ef,hQf,hef,hf⟩ := NativeFlowBudget.exists_budget b
    (NativePolynomialBudget.heightPolynomial lpWidth) flowWidth flowTime flowOutput flowProgram flowCoeff
  let P : Polynomial ℕ := lpWidth.comp (1000000*(Polynomial.X+1)^6+1)+
    lpTime.comp (1000000*(Polynomial.X+1)^6)+Polynomial.C allowance+1
  obtain ⟨Ql,el,hQl,hel,hl⟩ := NativePolynomialBudget.exists_majorant P
  refine ⟨Qr+Ql+Qf,max (max er el) ef,by omega,by have hh := Nat.le_max_right (max er el) ef; omega,?_⟩
  intro n load k h R hn hload hk hh
  have hflow := hf n load k h R hn hload hk hh
  have hlp := hl R
  simp only [P,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one] at hlp
  have hrl := monomial_sum Qr Ql er el R
  have hall := monomial_sum (Qr+Ql) Qf (max er el) ef R
  have hround := hr R
  dsimp only at hflow ⊢
  omega

end Lax263307Proofs.NativeOracleBudget
