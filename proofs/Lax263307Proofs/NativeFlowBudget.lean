import Lax263307Proofs.NativePolynomialBudget
import Lax263307Proofs.NativeSeparatorOutput

set_option maxHeartbeats 1500000

namespace Lax263307Proofs.NativeFlowBudget

open Lax455465Proofs NativeLargeCapacity NativeLargeResources NativeUniformFlow

noncomputable def numeratorPolynomial (b : ℕ) : Polynomial ℕ :=
  Polynomial.C b*(2*Polynomial.X+1)*(2*Polynomial.X)*(2*Polynomial.X)*(3*Polynomial.X)

noncomputable def resourcePolynomial (b : ℕ) : Polynomial ℕ :=
  Polynomial.C b+Polynomial.X+Polynomial.X+Polynomial.X+Polynomial.X+(2*Polynomial.X+1)+
    2*Polynomial.X+2*Polynomial.X+3*Polynomial.X+Polynomial.C b*(2*Polynomial.X+1)+
    Polynomial.C b*(2*Polynomial.X+1)*(2*Polynomial.X)+
    Polynomial.C b*(2*Polynomial.X+1)*(2*Polynomial.X)*(2*Polynomial.X)+
    2*numeratorPolynomial b+Polynomial.X*Polynomial.X+2*(Polynomial.X*Polynomial.X*Polynomial.X)+20

noncomputable def heightPolynomial (b : ℕ) (hp : Polynomial ℕ) : Polynomial ℕ :=
  hp+numeratorPolynomial b+resourcePolynomial b+Polynomial.X+30

noncomputable def lengthPolynomial : Polynomial ℕ := 2+4*Polynomial.X+8*Polynomial.X*Polynomial.X

noncomputable def queryPolynomial (b : ℕ) (hp : Polynomial ℕ) : Polynomial ℕ :=
  lengthPolynomial*(heightPolynomial b hp+Polynomial.X+4)

noncomputable def widthPolynomial (b : ℕ) (hp wp tp op : Polynomial ℕ) (p : Lax808846.Ram.Program) : Polynomial ℕ :=
  2*wp.comp (queryPolynomial b hp+1)+heightPolynomial b hp+
    (8*Polynomial.X*Polynomial.X+6*Polynomial.X+40)+queryPolynomial b hp+
    tp.comp (queryPolynomial b hp)+op.comp (queryPolynomial b hp)+Polynomial.C (RamVirtualConstants.allowance p)+20

noncomputable def spacePolynomial (b : ℕ) (hp tp : Polynomial ℕ) : Polynomial ℕ :=
  lengthPolynomial+tp.comp (queryPolynomial b hp)+Polynomial.X+2

noncomputable def splitPolynomial (b : ℕ) (hp tp : Polynomial ℕ)
    (p : Lax808846.Ram.Program) (coeff : List ℕ) : Polynomial ℕ :=
  488*Polynomial.X*Polynomial.X+56*Polynomial.X+36+
    ((12*queryPolynomial b hp+39)*lengthPolynomial+Polynomial.C (6*coeff.length+29))+
    ((tp.comp (queryPolynomial b hp)+1)*(Polynomial.C (4*p.length+104)+32*tp.comp (queryPolynomial b hp))+18)

noncomputable def timePolynomial (b : ℕ) (hp tp : Polynomial ℕ)
    (p : Lax808846.Ram.Program) (coeff : List ℕ) : Polynomial ℕ :=
  14*Polynomial.X+8+
    ((21*Polynomial.X+(168*Polynomial.X+132+splitPolynomial b hp tp p coeff)+62)*Polynomial.X+12)+
    37*(Polynomial.X+1)+10

private theorem logarithm_bound (n R : ℕ) (hn : n≤R) : Nat.log2 (2*n)+1≤2*R+1 := by
  have h : Nat.log2 (2*n)≤2*n := by rw [Nat.log2_eq_log_two]; exact Nat.log_le_self 2 (2*n)
  omega

theorem height_bound (b n load k h R : ℕ) (hp : Polynomial ℕ)
    (hn : n≤R) (hl : load≤R) (hk : k≤R) (hh : h≤hp.eval R) :
    heightExponent b n load k h≤(heightPolynomial b hp).eval R := by
  have hlog := logarithm_bound n R hn
  have hnum : numerator b n n k≤(numeratorPolynomial b).eval R := by
    simp only [numeratorPolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
    dsimp only [numerator]
    gcongr
  have hres : resource b n n load k≤(resourcePolynomial b).eval R := by
    simp only [resourcePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
    dsimp only [resource,denominator]
    gcongr
  simp only [heightPolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
  dsimp only [heightExponent]
  omega

theorem query_bound (b n H R : ℕ) (hp : Polynomial ℕ)
    (hn : n≤R) (hH : H≤(heightPolynomial b hp).eval R) :
    NativeFlowQueryResources.sizeBound n H≤(queryPolynomial b hp).eval R := by
  simp only [queryPolynomial,lengthPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  dsimp only [NativeFlowQueryResources.sizeBound,NativeSplitInput.wordLength]
  gcongr

theorem width_bound (b n H R : ℕ) (hp wp tp op : Polynomial ℕ) (p : Lax808846.Ram.Program)
    (hn : n≤R) (hH : H≤(heightPolynomial b hp).eval R) :
    wordHeight n H p wp tp op≤(widthPolynomial b hp wp tp op p).eval R := by
  have hS := query_bound b n H R hp hn hH
  have hw := NativeFlowQueryResources.eval_mono wp (Nat.add_le_add_right hS 1)
  have ht := NativeFlowQueryResources.eval_mono tp hS
  have ho := NativeFlowQueryResources.eval_mono op hS
  simp only [widthPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_ofNat,Polynomial.eval_one]
  dsimp only [wordHeight,shape]
  gcongr

theorem space_bound (b n H R : ℕ) (hp tp : Polynomial ℕ)
    (hn : n≤R) (hH : H≤(heightPolynomial b hp).eval R) :
    spaceBound n H tp≤(spacePolynomial b hp tp).eval R := by
  have hS := query_bound b n H R hp hn hH
  have ht := NativeFlowQueryResources.eval_mono tp hS
  simp only [spacePolynomial,lengthPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_ofNat]
  dsimp only [spaceBound,NativeSplitInput.wordLength]
  gcongr

theorem time_bound (b n H R : ℕ) (hp tp : Polynomial ℕ)
    (p : Lax808846.Ram.Program) (coeff : List ℕ)
    (hn : n≤R) (hH : H≤(heightPolynomial b hp).eval R) :
    NativeSeparatorOutput.timeBound n H p coeff tp≤(timePolynomial b hp tp p coeff).eval R := by
  have hS := query_bound b n H R hp hn hH
  have ht := NativeFlowQueryResources.eval_mono tp hS
  have hs : (2*n).size≤2*n+1 := Nat.size_le.mpr (by
    have hh : 2*n<2^(2*n) := Nat.lt_two_pow_self
    exact hh.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  have hsplit := NativeUniformFlow.cost_mono n R _ _ _ _ p coeff hn hS ht
  have he : NativeSplitOracle.cost R p coeff (tp.eval ((queryPolynomial b hp).eval R))
      ((queryPolynomial b hp).eval R)=(splitPolynomial b hp tp p coeff).eval R := by
    simp only [splitPolynomial,lengthPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_comp,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
    dsimp only [NativeSplitOracle.cost,NativeSplitInput.wordLength]
    ring
  rw [he] at hsplit
  have hc : callbackTime n H p coeff tp≤168*R+132+(splitPolynomial b hp tp p coeff).eval R := by
    dsimp only [callbackTime]
    omega
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one]
  dsimp only [NativeSeparatorOutput.timeBound,NativeSeparatorProgram.timeBound]
  gcongr

/-- Guard, workspace and complete separator time have one fixed monomial
majorant in the root resource. All constants precede every input and word width. -/
theorem exists_budget (b : ℕ) (hp wp tp op : Polynomial ℕ)
    (p : Lax808846.Ram.Program) (coeff : List ℕ) :
    ∃ Q e : ℕ,0<Q ∧ 0<e ∧ ∀ n load k h R,n≤R → load≤R → k≤R → h≤hp.eval R →
      let H := heightExponent b n load k h
      wordHeight n H p wp tp op+spaceBound n H tp+NativeSeparatorOutput.timeBound n H p coeff tp≤Q*(R+1)^e := by
  let P := widthPolynomial b hp wp tp op p+spacePolynomial b hp tp+timePolynomial b hp tp p coeff
  obtain ⟨Q,e,hQ,he,hm⟩ := NativePolynomialBudget.exists_majorant P
  refine ⟨Q,e,hQ,he,?_⟩
  intro n load k h R hn hl hk hh
  have hH := height_bound b n load k h R hp hn hl hk hh
  have hw := width_bound b n _ R hp wp tp op p hn hH
  have hs := space_bound b n _ R hp tp hn hH
  have ht := time_bound b n _ R hp tp p coeff hn hH
  have hb := hm R
  simp only [P,Polynomial.eval_add] at hb
  dsimp only
  omega

end Lax263307Proofs.NativeFlowBudget
