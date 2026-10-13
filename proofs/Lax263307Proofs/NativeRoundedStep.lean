import Lax263307.NativeRoundedStep
import Lax263307Proofs.RoundedOracleSearch
import Lax109476Proofs.RamReadBody
import Lax109476Proofs.RamArrayRelabel
import Lax109476Proofs.RamWriteVector
import Lax109476Proofs.RamAutomaticLayout
import Lax109476Proofs.RamEllipsoidBitBounds
import Mathlib.Tactic

set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace Lax263307Proofs.NativeRoundedStep

open Matrix
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax109476Proofs
open RamRationalArrays RamEllipsoidStep RamMatrixStorage RationalArithmeticBounds
open Lax109476.RationalEncoding

def body {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) : List ℕ :=
  WordDecoding.encodeRows A ++ encodeVector a ++ encodeVector c

def rename (a : String) : String :=
  if a = "lp.A.s" then "ell.shape.s" else
  if a = "lp.A.n" then "ell.shape.n" else
  if a = "lp.A.d" then "ell.shape.d" else
  if a = "lp.b.s" then "ell.normal.s" else
  if a = "lp.b.n" then "ell.normal.n" else
  if a = "lp.b.d" then "ell.normal.d" else
  if a = "lp.c.s" then "ell.center.s" else
  if a = "lp.c.n" then "ell.center.n" else
  if a = "lp.c.d" then "ell.center.d" else
  if a = "ell.shape.s" then "lp.A.s" else
  if a = "ell.shape.n" then "lp.A.n" else
  if a = "ell.shape.d" then "lp.A.d" else
  if a = "ell.normal.s" then "lp.b.s" else
  if a = "ell.normal.n" then "lp.b.n" else
  if a = "ell.normal.d" then "lp.b.d" else
  if a = "ell.center.s" then "lp.c.s" else
  if a = "ell.center.n" then "lp.c.n" else
  if a = "ell.center.d" then "lp.c.d" else a

theorem rename_involutive : Function.Involutive rename := by
  intro a
  by_cases h0 : a = "lp.A.s"
  · subst a
    rfl
  by_cases h1 : a = "lp.A.n"
  · subst a
    rfl
  by_cases h2 : a = "lp.A.d"
  · subst a
    rfl
  by_cases h3 : a = "lp.b.s"
  · subst a
    rfl
  by_cases h4 : a = "lp.b.n"
  · subst a
    rfl
  by_cases h5 : a = "lp.b.d"
  · subst a
    rfl
  by_cases h6 : a = "lp.c.s"
  · subst a
    rfl
  by_cases h7 : a = "lp.c.n"
  · subst a
    rfl
  by_cases h8 : a = "lp.c.d"
  · subst a
    rfl
  by_cases h9 : a = "ell.shape.s"
  · subst a
    rfl
  by_cases h10 : a = "ell.shape.n"
  · subst a
    rfl
  by_cases h11 : a = "ell.shape.d"
  · subst a
    rfl
  by_cases h12 : a = "ell.normal.s"
  · subst a
    rfl
  by_cases h13 : a = "ell.normal.n"
  · subst a
    rfl
  by_cases h14 : a = "ell.normal.d"
  · subst a
    rfl
  by_cases h15 : a = "ell.center.s"
  · subst a
    rfl
  by_cases h16 : a = "ell.center.n"
  · subst a
    rfl
  by_cases h17 : a = "ell.center.d"
  · subst a
    rfl
  simp only [rename, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, if_false]

def metadata : Com :=
  .seq (.assign "lp.m" (.var "vec.n"))
  (.seq (.assign "lp.n" (.var "vec.n"))
  (.seq (.assign "decode.count" (.mul (.var "vec.n") (.var "vec.n")))
  (.seq (.assign "input.remaining" (.mul (.lit 3)
    (.add (.var "decode.count") (.mul (.lit 2) (.var "vec.n")))))
    (.assign "input.valid" (.lit 1)))))

def readState : Com :=
  .seq (.read "vec.n") (.seq (.read "iter.k")
    (.seq metadata (.seq (RamArrayRelabel.command rename RamReadBody.readBody)
      (.assign "vec.n" (.var "lp.n")))))

def writeState : Com :=
  .seq (.assign "output.count" (.mul (.var "vec.n") (.var "vec.n")))
  (.seq (RamWriteVector.writePrefix "ell.nextshape")
  (.seq (.assign "output.count" (.var "vec.n"))
    (RamWriteVector.writePrefix "ell.nextcenter")))

def command : Com := .seq readState (.seq ellipsoidStep writeState)

theorem metadata_spec (B n : ℕ) (hn : n < B) (hnn : n * n < B)
    (hcount : 3 * (n * n + 2 * n) < B) (hthree : 3 < B) :
    Spec B (fun σ => σ.vars "vec.n" = n) metadata
      (fun _ τ => τ.vars "lp.m" = n ∧ τ.vars "lp.n" = n ∧
        τ.vars "decode.count" = n * n ∧ τ.vars "input.remaining" = 3 * (n * n + 2 * n) ∧
        τ.vars "input.valid" = 1 ∧ τ.vars "vec.n" = n) 18 := by
  have htwo : 2 < B := by omega
  have hmul : 2 * n < B := by omega
  have hadd : n * n + 2 * n < B := by omega
  rintro σ hσ
  run_vcg
  all_goals simp_all [Env.setVar]

theorem write_state_spec {n : ℕ} (B M : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (h1 : 1 < B) (hM : M < B) (hn : n < B) (hnn : n * n < B)
    (hA : ∀ i j, Height (A i j) M) (hc : ∀ i, Height (c i) M) :
    Spec B (fun σ => Represents "ell.nextshape" (flatten A) σ ∧
        Represents "ell.nextcenter" (List.ofFn c) σ ∧ σ.vars "vec.n" = n)
      writeState
      (fun σ τ => τ.out = σ.out ++ (flatten A).flatMap encodeRational ++ encodeVector c)
      (35 * (n * n + n) + 20) := by
  have hflat : ∀ q ∈ flatten A, Height q M := by
    intro q hq
    simp only [flatten, List.mem_ofFn] at hq
    obtain ⟨i, rfl⟩ := hq
    exact hA i.divNat i.modNat
  have hvec : ∀ q ∈ List.ofFn c, Height q M := by
    intro q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact hc i
  rintro σ ⟨hσA, hσc, hσn⟩
  have hr₁ : Run B (.assign "output.count" (.mul (.var "vec.n") (.var "vec.n")))
      σ (σ.setVar "output.count" (n * n)) 4 := by
    apply Run.assign
    simpa only [Bop.apply_mul, hσn] using
      evalB_bin (op := .mul) (evalB_var (B := B) (σ := σ) (x := "vec.n") (hσn ▸ hn))
        (evalB_var (B := B) (σ := σ) (x := "vec.n") (hσn ▸ hn))
        (by simpa only [Bop.apply_mul, hσn] using hnn)
  obtain ⟨τ, hr₂, hout₂⟩ := RamWriteVector.writePrefix_spec B M (n * n) "ell.nextshape"
    (flatten A) h1 hM hnn (by simp [flatten]) hflat
    (σ.setVar "output.count" (n * n)) ⟨hσA, by simp⟩
  have hτn : τ.vars "vec.n" = n := ((hr₁.seq hr₂).frame_var _ (by decide)).trans hσn
  have hτc : Represents "ell.nextcenter" (List.ofFn c) τ :=
    RamReadBody.represents_frame _ _ hσc (hr₁.seq hr₂) (by decide)
  have hr₃ : Run B (.assign "output.count" (.var "vec.n")) τ (τ.setVar "output.count" n) 2 := by
    apply Run.assign
    simpa only [hτn] using evalB_var (B := B) (σ := τ) (x := "vec.n") (hτn ▸ hn)
  obtain ⟨υ, hr₄, hout₄⟩ := RamWriteVector.writePrefix_spec B M n "ell.nextcenter"
    (List.ofFn c) h1 hM hn (by simp) hvec
    (τ.setVar "output.count" n) ⟨hτc, by simp⟩
  refine ⟨υ, (hr₁.seq (hr₂.seq (hr₃.seq hr₄))).mono (by omega), ?_⟩
  change υ.out = _
  rw [hout₄]
  change τ.out ++ _ = _
  rw [hout₂]
  have htakeA : (flatten A).take (n * n) = flatten A := List.take_of_length_le (by simp [flatten])
  have htakec : (List.ofFn c).take n = List.ofFn c := List.take_of_length_le (by simp)
  simp only [Env.setVar, htakeA, htakec, encodeVector, List.append_assoc]

theorem body_length {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ) :
    (body A a c).length = 3 * (n * n + 2 * n) := by
  simp only [body, List.length_append]
  rw [WordDecoding.encodeRows_length n n A, WordDecoding.encodeVector_length n a,
    WordDecoding.encodeVector_length n c]
  ring

theorem read_state_spec {n : ℕ} (B H k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ)
    (hthree : 3 < B) (hH : 1 ≤ H) (hHB : H < B) (hnB : n < B) (hnnB : n * n < B)
    (hbodyB : (body A a c).length < B) (hwords : ∀ x ∈ body A a c, x ≤ H) :
    Spec B (fun σ => Extents "ell.shape" (n * n) σ ∧ Extents "ell.normal" n σ ∧
        Extents "ell.center" n σ ∧ Workspace n σ ∧
        σ.inp = n :: k :: body A a c ∧ σ.InpBounded B)
      readState
      (fun σ τ => Represents "ell.shape" (flatten A) τ ∧ Represents "ell.normal" (List.ofFn a) τ ∧
        Represents "ell.center" (List.ofFn c) τ ∧ Workspace n τ ∧
        τ.vars "vec.n" = n ∧ τ.vars "iter.k" = k ∧ τ.inp = [] ∧ τ.out = σ.out)
      ((36 * H.size + 115) * (n * n + 2 * n) + 110) := by
  let P : Lax109476.LinearProgram.Program ℚ n n := ⟨A, a, c⟩
  have hread := RamArrayRelabel.spec_relabel rename rename_involutive.injective
    (RamReadBody.readBody_valid_spec B H n n P (by omega) hHB hH hnB hnB hnnB
      hbodyB hwords)
  rintro σ ⟨hσA, hσa, hσc, hσwork, hσinp, hσbound⟩
  let σ₁ : Env := {σ.setVar "vec.n" n with inp := k :: body A a c}
  let σ₂ : Env := {σ₁.setVar "iter.k" k with inp := body A a c}
  have hr₁ : Run B (.read "vec.n") σ σ₁ 1 := Run.read hσinp
  have hr₂ : Run B (.read "iter.k") σ₁ σ₂ 1 := Run.read rfl
  have hhead := hr₁.seq hr₂
  have hcount : 3 * (n * n + 2 * n) < B := by rwa [body_length] at hbodyB
  obtain ⟨τ, hr₃, hτm, hτn, hτcount, hτremaining, hτvalid, hτvec⟩ :=
    metadata_spec B n hnB hnnB hcount hthree σ₂ (by simp [σ₂, σ₁])
  have hfirst := hhead.seq hr₃
  have hτinp : τ.inp = body A a c := (hr₃.frame_inp (by decide)).trans rfl
  have hτA := RamAdvanceState.extents_of_run hfirst "ell.shape" (n * n) hσA
  have hτa := RamAdvanceState.extents_of_run hfirst "ell.normal" n hσa
  have hτc := RamAdvanceState.extents_of_run hfirst "ell.center" n hσc
  have hviewA : Extents "lp.A" (n * n) (RamArrayRelabel.view rename τ) := by
    simpa [Extents, RamArrayRelabel.view, rename, Equiv.swap_apply_def] using hτA
  have hviewa : Extents "lp.b" n (RamArrayRelabel.view rename τ) := by
    simpa [Extents, RamArrayRelabel.view, rename, Equiv.swap_apply_def] using hτa
  have hviewc : Extents "lp.c" n (RamArrayRelabel.view rename τ) := by
    simpa [Extents, RamArrayRelabel.view, rename, Equiv.swap_apply_def] using hτc
  obtain ⟨υ, hr₄, hυA, hυa, hυc, hυinp, _, _, _, _, hυn, _⟩ := hread τ
    ⟨hviewA, hviewa, hviewc, hτinp, by change τ.vars "input.remaining" = (body A a c).length; rw [body_length]; exact hτremaining,
      hτvalid, hfirst.inpBounded hσbound, hτm, hτn, hτcount⟩
  have hυA' : Represents "ell.shape" (flatten A) υ := by
    simpa [RamArrayRelabel.view, RamRationalArrays.Represents, rename, P] using hυA
  have hυa' : Represents "ell.normal" (List.ofFn a) υ := by
    simpa [RamArrayRelabel.view, RamRationalArrays.Represents, rename, P] using hυa
  have hυc' : Represents "ell.center" (List.ofFn c) υ := by
    simpa [RamArrayRelabel.view, RamRationalArrays.Represents, rename, P] using hυc
  have hυn' : υ.vars "lp.n" = n := hυn
  have hr₅ : Run B (.assign "vec.n" (.var "lp.n")) υ (υ.setVar "vec.n" n) 2 := by
    apply Run.assign
    simpa only [hυn'] using evalB_var (B := B) (σ := υ) (x := "lp.n") (hυn' ▸ hnB)
  have hrun := hr₁.seq (hr₂.seq (hr₃.seq (hr₄.seq hr₅)))
  refine ⟨_, hrun.mono (by rw [show n * n + n + n = n * n + 2 * n by omega]; omega), ?_, ?_, ?_, RamAdvanceState.workspace_of_run hrun n hσwork,
    by simp, ?_, ?_, ?_⟩
  · exact hυA'
  · exact hυa'
  · exact hυc'
  · have hk : υ.vars "iter.k" = k := (hr₃.seq hr₄).frame_var "iter.k" (by decide)
    simpa [σ₂, σ₁] using hk
  · exact hυinp
  · exact hrun.out_eq (by decide)

def cost (n H M : ℕ) : ℕ :=
  ((36 * H.size + 115) * (n * n + 2 * n) + 110) +
    RamEllipsoidStep.stepCost n H M + (35 * (n * n + n) + 20)

theorem command_spec {n : ℕ} (B H M k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ)
    (hn : 2 ≤ n) (hH : 1 ≤ H) (hA : ∀ i j, Height (A i j) H)
    (ha : ∀ i, Height (a i) H) (hc : ∀ i, Height (c i) H)
    (hqpos : 0 < a ⬝ᵥ (A *ᵥ a)) (hnM : n * n ≤ M)
    (hFM : RamEllipsoidForm.formHeight n H ≤ M)
    (hDM : 2 ^ (2 * k + 3 * n + 9) ≤ M) (hEM : 2 ^ (2 * n + 4) ≤ M)
    (hB : 2 * (RamShapeCoordinate.shapeCap (RamEllipsoidCoefficients.coefficientCap M)) ^ 2 + 3 < B)
    (hbodyB : (body A a c).length < B) (hwords : ∀ x ∈ body A a c, x ≤ H) :
    Spec B (fun σ => Extents "ell.shape" (n * n) σ ∧ Extents "ell.normal" n σ ∧
        Extents "ell.center" n σ ∧ Workspace n σ ∧
        σ.inp = n :: k :: body A a c ∧ σ.InpBounded B)
      command
      (fun σ τ => τ.out = σ.out ++
        (flatten (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
          (EllipsoidIteration.stepAccuracy n))).flatMap encodeRational ++
        encodeVector (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9))))
      (cost n H M) := by
  let S := RamShapeCoordinate.shapeCap (RamEllipsoidCoefficients.coefficientCap M)
  have hcaps := RamEllipsoidWordBounds.unified_word_bounds B M n hn hnM hB
  have h1 : 1 < B := by omega
  have hthree : 3 < B := by omega
  have hMB : M < B := hcaps.2.1
  have hHM : H ≤ M := ((RamDotProduct.cap_ge n H hH).2.trans
    (RamEllipsoidForm.formHeight_ge n H hH)).trans hFM
  have hHB : H < B := hHM.trans_lt hMB
  have hnB : n < B := hcaps.2.2.2.1
  have hnnB : n * n < B := by simpa only [pow_two] using hcaps.2.2.1
  have hSpos : 1 ≤ S := by
    have hp : 1 ≤ (RamEllipsoidCoefficients.coefficientCap M + 1) ^ 8 := by
      exact Nat.one_le_pow 8 _ (by omega)
    dsimp [S, RamShapeCoordinate.shapeCap]
    omega
  have hSB : S < B := by change 2 * S ^ 2 + 3 < B at hB; nlinarith [le_self_pow hSpos (by decide : (2 : ℕ) ≠ 0)]
  have hnew := RamEllipsoidStoredBounds.step_stored_bounds n H M k A a c hH hA ha hc
    ((Nat.le_mul_self n).trans hnM) hFM hDM hEM
  rintro σ hσ
  obtain ⟨τ, hr₁, hτA, hτa, hτc, hτw, hτn, hτk, _, hτout⟩ :=
    read_state_spec B H k A a c hthree hH hHB hnB hnnB hbodyB hwords σ hσ
  obtain ⟨υ, hr₂, hυc, hυA, _, _, hυn, _⟩ :=
    RamEllipsoidStep.ellipsoidStep_spec B n H M k A a c hn hH hA ha hc hqpos hnM hFM hDM hEM hB
      τ ⟨hτA, hτa, hτc, hτw, hτn, hτk⟩
  obtain ⟨ξ, hr₃, hξout⟩ := write_state_spec B S
    (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9)) (EllipsoidIteration.stepAccuracy n))
    (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9))) h1 hSB hnB hnnB hnew.2 hnew.1
      υ ⟨hυA, hυc, hυn⟩
  have hυout : υ.out = σ.out := (hr₂.out_eq (by decide)).trans hτout
  refine ⟨ξ, (hr₁.seq (hr₂.seq hr₃)).mono (by dsimp [cost]; omega), ?_⟩
  change ξ.out = _
  rw [hξout, hυout]

def costEnvelope (X : ℕ) : ℕ :=
  ((36 * X + 115) * (X * X + 2 * X) + 110) +
    ((144 * ((X + 1) * (2 * X + 3) + 1) + 220) * X ^ 2 +
      (144 * ((X + 1) * (2 * ((X + 1) * (2 * X + 3) + 1) + 3) + 1) + 292) * X +
      (2880 * X + 7559) * X + (14976 * X + 36767) * (X * X) + 582 * X + 1000) +
    (35 * (X * X + X) + 20)

theorem cost_polynomial (n H M : ℕ) :
    10 * cost n H M + 1 ≤ 1000000 * (n + H.size + M.size + 1) ^ 4 := by
  let X := n + H.size + M.size + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hn : n ≤ X := by dsimp [X]; omega
  have hH : H.size ≤ X := by dsimp [X]; omega
  have hM : M.size ≤ X := by dsimp [X]; omega
  have hstep := RamEllipsoidStep.stepCost_polynomial n H M
  have hcost : cost n H M ≤ costEnvelope X := by
    unfold cost costEnvelope
    apply (Nat.add_le_add_right (Nat.add_le_add_left hstep _) _).trans
    gcongr
  have hpoly : costEnvelope X = 864 * X ^ 4 + 17748 * X ^ 3 + 43689 * X ^ 2 + 10426 * X + 1130 := by
    unfold costEnvelope
    ring
  have h0 : 1 ≤ X ^ 4 := Nat.one_le_pow 4 X (by omega)
  have h1 : X ≤ X ^ 4 := le_self_pow hX (by decide)
  have h2 : X ^ 2 ≤ X ^ 4 := Nat.pow_le_pow_right hX (by decide)
  have h3 : X ^ 3 ≤ X ^ 4 := Nat.pow_le_pow_right hX (by decide)
  rw [hpoly] at hcost
  change 10 * cost n H M + 1 ≤ 1000000 * X ^ 4
  nlinarith

def ext (n : ℕ) (a : String) : ℕ :=
  if a ∈ ["ell.shape.s", "ell.shape.n", "ell.shape.d",
      "ell.nextshape.s", "ell.nextshape.n", "ell.nextshape.d"] then n * n
  else if a ∈ ["ell.coeff.s", "ell.coeff.n", "ell.coeff.d"] then 5 else n

def layout := RamAutomaticLayout.layout command
def program : Lax808846.Ram.Program := Lax808846Proofs.Compile.compileProgram layout command

theorem initial_extents (n : ℕ) (input : List ℕ) :
    Extents "ell.shape" (n * n) (initEnv (ext n) input) ∧
      Extents "ell.normal" n (initEnv (ext n) input) ∧
      Extents "ell.center" n (initEnv (ext n) input) ∧
      Workspace n (initEnv (ext n) input) := by
  simp [Extents, Workspace, initEnv, ext]

theorem compiled_runs_to {n : ℕ} (v w H M k : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ)
    (hv : 0 < v) (hw : v + RamTransfer.layoutAllowance layout ≤ w)
    (hn : 2 ≤ n) (hH : 1 ≤ H) (hA : ∀ i j, Height (A i j) H)
    (ha : ∀ i, Height (a i) H) (hc : ∀ i, Height (c i) H)
    (hqpos : 0 < a ⬝ᵥ (A *ᵥ a)) (hnM : n * n ≤ M)
    (hFM : RamEllipsoidForm.formHeight n H ≤ M)
    (hDM : 2 ^ (2 * k + 3 * n + 9) ≤ M) (hEM : 2 ^ (2 * n + 4) ≤ M)
    (hB : 2 * (RamShapeCoordinate.shapeCap (RamEllipsoidCoefficients.coefficientCap M)) ^ 2 + 3 < 2 ^ v)
    (hbodyB : (body A a c).length < 2 ^ v) (hwords : ∀ x ∈ body A a c, x ≤ H)
    (hinput : ∀ x ∈ n :: k :: body A a c, x < 2 ^ v) :
    ∃ t ≤ 10 * cost n H M + 1, Lax808846.Ram.RunsTo w program
      (n :: k :: body A a c)
      ((flatten (EllipsoidCenter.roundedStepShape n A a (2 ^ (2 * k + 3 * n + 9))
        (EllipsoidIteration.stepAccuracy n))).flatMap encodeRational ++
        encodeVector (EllipsoidCenter.roundedCenter n A a c (2 ^ (2 * k + 3 * n + 9)))) t := by
  have hinit := initial_extents n (n :: k :: body A a c)
  obtain ⟨τ, hr, hout⟩ := command_spec (2 ^ v) H M k A a c hn hH hA ha hc hqpos hnM hFM hDM hEM
    hB hbodyB hwords (initEnv (ext n) (n :: k :: body A a c))
    ⟨hinit.1, hinit.2.1, hinit.2.2.1, hinit.2.2.2, rfl, hinput⟩
  obtain ⟨K, hK, hbs⟩ := hr
  obtain ⟨t, ht, hrun⟩ := Lax808846Proofs.Simulation.compileProgram_runsTo
    (RamTransfer.layout_fits hv hw) (RamAutomaticLayout.layout_ok command) hinput hbs
  refine ⟨t, ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 10 hK) 1), ?_⟩
  simpa only [program, layout, hout, initEnv, List.nil_append] using hrun

theorem encoded_words {n : ℕ} (H : ℕ) (hH : 1 ≤ H)
    (A : Matrix (Fin n) (Fin n) ℚ) (a c : Fin n → ℚ)
    (hA : ∀ i j, Height (A i j) H) (ha : ∀ i, Height (a i) H)
    (hc : ∀ i, Height (c i) H) : ∀ x ∈ body A a c, x ≤ H := by
  have rational_words : ∀ q : ℚ, Height q H → ∀ x ∈ encodeRational q, x ≤ H := by
    intro q hq x hx
    simp only [encodeRational, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · split_ifs <;> omega
    · exact hq.1
    · exact hq.2
  have vector_words : ∀ v : Fin n → ℚ, (∀ i, Height (v i) H) →
      ∀ x ∈ encodeVector v, x ≤ H := by
    intro v hv x hx
    obtain ⟨q, hq, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    exact rational_words _ (hv i) x hx
  intro x hx
  simp only [body, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨row, hrow, hx⟩ := List.mem_flatten.mp hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    exact vector_words (A i) (hA i) x hx
  · exact vector_words a ha x hx
  · exact vector_words c hc x hx

theorem magnitude_polynomial (n h k : ℕ) :
    RamEllipsoidBitBounds.magnitudeExponent n h k ≤ 26 * (n + h + k + 1) ^ 3 := by
  let X := n + h + k + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hn : n ≤ X := by dsimp [X]; omega
  have hh : h ≤ X := by dsimp [X]; omega
  have hk : k ≤ X := by dsimp [X]; omega
  have hn1 : n + 1 ≤ X := by dsimp [X]; omega
  have hnn : n * n ≤ X ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hn hn
  have hform : RamEllipsoidBitBounds.formExponent n h ≤ (2 * (2 * X * X) + 1) * X := by
    unfold RamEllipsoidBitBounds.formExponent
    gcongr
    dsimp [X]
    omega
  have h1 : X ≤ X ^ 3 := le_self_pow hX (by decide)
  have h2 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX (by decide)
  have h0 : 1 ≤ X ^ 3 := Nat.one_le_pow 3 X (by omega)
  change RamEllipsoidBitBounds.formExponent n h + n * n + 2 * k + 5 * n + 13 ≤ 26 * X ^ 3
  nlinarith only [hform, hnn, hk, hn, h0, h1, h2]

/--
---
conclusion: Lax263307.NativeRoundedStep.exists_program
---
Compile the complete reader/update/writer command. The native magnitude and
word guards are bounded by a cubic polynomial in n+h+k; its instruction
bound is polynomial of degree twelve in those same input parameters.
-/
theorem exists_program : ∃ p : Lax808846.Ram.Program, ∃ c : ℕ, 0 < c ∧
    ∀ (n k h : ℕ), 2 ≤ n → 1 ≤ h →
      ∀ (state : Lax263307.RoundedOracleSearch.State n) (a : Fin n → ℤ),
        (∀ i j, Lax263307.NativeRoundedStep.height (state.1 i j) h) →
        (∀ i, Lax263307.NativeRoundedStep.height (Lax263307.RoundedOracleSearch.rationalNormal a i) h) →
        (∀ i, Lax263307.NativeRoundedStep.height (state.2 i) h) →
        0 < Lax263307.RoundedOracleSearch.rationalNormal a ⬝ᵥ
          (state.1 *ᵥ Lax263307.RoundedOracleSearch.rationalNormal a) →
        ∀ w : ℕ, c * (n + h + k + 1) ^ 12 ≤ w →
          ∃ t ≤ c * (n + h + k + 1) ^ 12, Lax808846.Ram.RunsTo w p
            (Lax263307.NativeRoundedStep.encodeInput k state a)
            (Lax263307.NativeRoundedStep.encodeOutput
              (Lax263307.RoundedOracleSearch.update k state a)) t := by
  let C := 1000000000000000 + RamTransfer.layoutAllowance layout
  refine ⟨program, C, by dsimp [C]; omega, ?_⟩
  intro n k h hn hh state a hA ha hc hpos w hw
  let X := n + h + k + 1
  let E := RamEllipsoidBitBounds.magnitudeExponent n h k
  let H := 2 ^ h
  let M := 2 ^ E
  let v := RamEllipsoidBitBounds.wordWidth n h k + 3 * (n * n + 2 * n) + h + k + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hnX : n ≤ X := by dsimp [X]; omega
  have hhX : h ≤ X := by dsimp [X]; omega
  have hkX : k ≤ X := by dsimp [X]; omega
  have h1 : X ≤ X ^ 3 := le_self_pow hX (by decide)
  have h2 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX (by decide)
  have h0 : 1 ≤ X ^ 3 := Nat.one_le_pow 3 X (by omega)
  have hE : E ≤ 26 * X ^ 3 := magnitude_polynomial n h k
  have hnn : n * n ≤ X ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hnX hnX
  have hvbound : v ≤ 2000 * X ^ 3 := by
    dsimp [v, RamEllipsoidBitBounds.wordWidth]
    change 64 * E + 224 + 3 * (n * n + 2 * n) + h + k + 1 ≤ _
    nlinarith only [hE, hnn, hnX, hhX, hkX, h0, h1, h2]
  have hX12 : X ^ 3 ≤ X ^ 12 := Nat.pow_le_pow_right hX (by decide)
  have h012 : 1 ≤ X ^ 12 := Nat.one_le_pow 12 X (by omega)
  have hwv : v + RamTransfer.layoutAllowance layout ≤ w := by
    change C * X ^ 12 ≤ w at hw
    have hallow := Nat.mul_le_mul_left (RamTransfer.layoutAllowance layout) h012
    dsimp [C] at hw
    nlinarith only [hw, hvbound, hX12, hallow]
  have hv : 0 < v := by dsimp [v]; omega
  have hH : 1 ≤ H := Nat.one_le_pow h 2 (by decide)
  have hparams := RamEllipsoidBitBounds.magnitude_parameters n h k
  have hguard := RamEllipsoidBitBounds.wordWidth_sufficient n h k v (by dsimp [v]; omega)
  have hlength : (body state.1 (Lax263307.RoundedOracleSearch.rationalNormal a) state.2).length < 2 ^ v := by
    rw [body_length]
    have hlen : 3 * (n * n + 2 * n) < v := by dsimp [v]; omega
    exact hlen.trans Nat.lt_two_pow_self
  have hwords := encoded_words H hH state.1 (Lax263307.RoundedOracleSearch.rationalNormal a) state.2 hA ha hc
  have hinput : ∀ x ∈ n :: k :: body state.1 (Lax263307.RoundedOracleSearch.rationalNormal a) state.2, x < 2 ^ v := by
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with hxn | hxk | hx
    · rw [hxn]
      have hnV : n < v := by dsimp [v]; nlinarith only [hn]
      exact hnV.trans Nat.lt_two_pow_self
    · rw [hxk]
      have hkV : k < v := by dsimp [v]; omega
      exact hkV.trans Nat.lt_two_pow_self
    · have hhV : h < v := by dsimp [v]; omega
      exact (hwords x hx).trans_lt (Nat.pow_lt_pow_right (by decide) hhV)
  obtain ⟨t, ht, hrun⟩ := compiled_runs_to v w H M k state.1
    (Lax263307.RoundedOracleSearch.rationalNormal a) state.2 hv hwv hn hH hA ha hc hpos
    hparams.1 hparams.2.1 hparams.2.2.1 hparams.2.2.2 hguard hlength hwords hinput
  have hsize : n + H.size + M.size + 1 ≤ 30 * X ^ 3 := by
    dsimp only [H, M]
    rw [Nat.size_pow, Nat.size_pow]
    have hs : n + h + 3 ≤ 3 * X := by dsimp [X]; omega
    nlinarith only [hE, hs, h1]
  have htime : 10 * cost n H M + 1 ≤ C * X ^ 12 := by
    calc
      _ ≤ 1000000 * (n + H.size + M.size + 1) ^ 4 := cost_polynomial n H M
      _ ≤ 1000000 * (30 * X ^ 3) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsize 4)
      _ = 810000000000 * X ^ 12 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by dsimp [C]; omega)
  refine ⟨t, ht.trans htime, ?_⟩
  have hgrid : Lax263307.RoundedOracleSearch.grid n k = 2 ^ (2 * k + 3 * n + 9) := by
    unfold Lax263307.RoundedOracleSearch.grid
    congr 1
    omega
  have hstep : Lax263307.RoundedOracleSearch.update k state a =
      (EllipsoidCenter.roundedStepShape n state.1
        (Lax263307.RoundedOracleSearch.rationalNormal a) (2 ^ (2 * k + 3 * n + 9))
        (EllipsoidIteration.stepAccuracy n),
       EllipsoidCenter.roundedCenter n state.1
        (Lax263307.RoundedOracleSearch.rationalNormal a) state.2 (2 ^ (2 * k + 3 * n + 9))) := by
    simp only [Lax263307.RoundedOracleSearch.update, Lax263307Proofs.RoundedOracleSearch.cached_eq, hgrid]
    rfl
  rw [hstep]
  exact hrun

end Lax263307Proofs.NativeRoundedStep
