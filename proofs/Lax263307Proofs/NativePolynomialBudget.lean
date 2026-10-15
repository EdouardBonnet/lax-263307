import Lax455465Proofs.RamPolynomial
import Lax263307Proofs.NativeOraclePrecision

namespace Lax263307Proofs.NativePolynomialBudget

open Lax455465Proofs

set_option maxHeartbeats 1000000

/-- A fixed coefficient list has a fixed monomial majorant. -/

theorem value_bound (cs : List ℕ) (x : ℕ) : RamPolynomial.value cs x≤cs.sum*(x+1)^cs.length := by
  induction cs with
  | nil => simp [RamPolynomial.value]
  | cons c cs ih =>
    have hp : 1≤(x+1)^cs.length := Nat.one_le_pow _ _ (by omega)
    have hc : c≤c*(x+1)^cs.length := Nat.le_mul_of_pos_right _ hp
    have hi := Nat.mul_le_mul_left x ih
    simp only [RamPolynomial.value,List.sum_cons,List.length_cons]
    calc
      c+x*RamPolynomial.value cs x≤c+x*(cs.sum*(x+1)^cs.length) := Nat.add_le_add_left hi _
      _≤c*(x+1)^cs.length+x*(cs.sum*(x+1)^cs.length) := Nat.add_le_add_right hc _
      _≤(c+cs.sum)*(x+1)^cs.length*(x+1) := by ring_nf; omega
      _=_ := by ring

/-- Choose constants once for a fixed polynomial, before the root input. -/
theorem exists_majorant (P : Polynomial ℕ) :
    ∃ Q e : ℕ,0<Q ∧ 0<e ∧ ∀ R,P.eval R≤Q*(R+1)^e := by
  obtain ⟨cs,hcs⟩ := RamPolynomial.exists_coefficients P
  refine ⟨cs.sum+1,cs.length+1,by omega,by omega,?_⟩
  intro R
  rw [←hcs]
  exact (value_bound cs R).trans (Nat.mul_le_mul (by omega)
    (Nat.pow_le_pow_right (by omega) (by omega)))

noncomputable def heightPolynomial (wp : Polynomial ℕ) : Polynomial ℕ :=
  80*(Polynomial.X+1)+(Polynomial.X+1)*(2*wp.comp (1000000*(Polynomial.X+1)^6)+1)+2*Polynomial.X+1

theorem height_bound (wp : Polynomial ℕ) (R : ℕ) :
    NativeOraclePrecision.roundedHeight wp R≤(heightPolynomial wp).eval R := by
  have hq := Lax263307Proofs.NativeProjectionQueryBounds.polynomial_bound R
  have hp := Lax263307Proofs.NativeFlowQueryResources.eval_mono wp hq
  simp only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  dsimp [NativeOraclePrecision.roundedHeight,NativeOraclePrecision.certificateHeight]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hp) 1)) _) _) _


end Lax263307Proofs.NativePolynomialBudget
