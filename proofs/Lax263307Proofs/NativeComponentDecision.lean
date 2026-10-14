import Lax263307Proofs.NativeComponentSum
import Lax263307Proofs.NativeComponentResources

namespace Lax263307Proofs.NativeComponentDecision

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeSignedArithmetic NativeRestrictionRead
open scoped NNRat

def height (n h : ℕ) : ℕ := 2^((h+1)*(n+1))
def wordHeight (n D k h : ℕ) : ℕ := 2*((h+1)*(n+1))+4*NativeComponentResources.span n D k+20
def timeBound (n h : ℕ) : ℕ := (36*((height n h)^2).size+258)*n+72

def command : Com := .seq NativeComponentSum.command NativeComponentTarget.command

/-- A single native component decision computes both the cost and the
recursive target. All precision guards are uniform in the subset R. -/
theorem command_spec (n D k h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (hn : 0<n) (hD : 0<D) (hx : ∀ v,Bounded (2^h) (x v : ℚ))
    (w : ℕ) (hw : wordHeight n D k h≤w) (R : Finset (Fin n)) :
    Spec (2^w) (fun σ => Data G (fun v => (x v : ℚ)) R σ ∧
      σ.vars "algorithm.D"=D ∧ σ.vars "conditioning.k"=k ∧
      3*n<(σ.arrs "lp.word").length ∧ 3*n≤(σ.arrs "sum.input").length)
      command (fun _ τ => Data G (fun v => (x v : ℚ)) R τ ∧
        τ.vars "component.target"=Lax263307.ComputedRounding.target (1/(D : ℚ)) (∑ v∈R,(x v : ℚ)) ∧
        τ.vars "component.active"=if (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈R,(x v : ℚ)) then 1 else 0)
      (timeBound n h) := by
  let L := (h+1)*(n+1)
  have hr := NativeMaskUnpack.card_bound R
  have hH : (2*(2^h))^(R.card+1)=2^((h+1)*(R.card+1)) := by
    have he : 2*2^h=2^(h+1) := by rw [pow_succ]; exact Nat.mul_comm _ _
    rw [he,pow_mul]
  have hHn : (2*(2^h))^(R.card+1)≤height n h := by
    rw [hH]
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.mul_le_mul_left _ (by omega)
  have hword := hw
  dsimp only [wordHeight] at hword
  have hWL : 2*L+4*NativeComponentResources.span n D k+20≤w := hw
  have hspan : n+20≤NativeComponentResources.span n D k := by dsimp [NativeComponentResources.span]; omega
  have hB : 2*(height n h)^2+3<2^w := NativeUniformWordGuards.virtual L w (by omega)
  have hN : 3*n+10<2^w := NativeUniformWordGuards.scalar _ w (by omega)
  have hBR : 2*((2*(2^h))^(R.card+1))^2+3<2^w :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hHn 2)) 3).trans_lt hB
  let qs := List.ofFn (fun i : Fin R.card => (x (label R i) : ℚ))
  have hqs : ∀ q∈qs,Bounded (2^h) q := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact hx _
  have hsum : Bounded (height n h) (∑ v∈R,(x v : ℚ)) := by
    have hb := NativeSumHeight.sum_bits h qs hqs
    have hle : 2^((h+1)*qs.length)≤height n h := Nat.pow_le_pow_right (by decide)
      (by simp only [qs,List.length_ofFn]; exact Nat.mul_le_mul_left _ (by omega))
    have he : qs.sum=∑ v∈R,(x v : ℚ) := NativeComponentSum.sum_labels R (fun v => (x v : ℚ))
    rw [he] at hb
    exact NativeSumHeight.weaken hle hb
  have hq : 0≤∑ v∈R,(x v : ℚ) := Finset.sum_nonneg (fun v _ => (x v).coe_nonneg)
  have htB : NativeComponentTarget.resource n D k (∑ v∈R,(x v : ℚ))<2^w :=
    NativeComponentResources.word_bound n D k L w _ hsum (by omega)
  rintro σ ⟨hd,hDσ,hkσ,hwordroom,hsumroom⟩
  obtain ⟨ν,r1,p1⟩ := NativeComponentSum.command_spec (2^w) (2^h) n G (fun v => (x v : ℚ)) R
    (Nat.one_le_pow _ _ (by decide)) hN hBR hx σ ⟨hd,by omega,by omega⟩
  obtain ⟨τ,r2,p2⟩ := NativeComponentTarget.command_spec (2^w) n D k _ hn hD hq htB ν
    ⟨p1.1.order,(r1.frame_var "algorithm.D" (by decide)).trans hDσ,
      (r1.frame_var "conditioning.k" (by decide)).trans hkσ,p1.2⟩
  have hsize : (((2*(2^h))^(R.card+1))^2).size≤((height n h)^2).size :=
    Nat.size_le_size (Nat.pow_le_pow_left hHn 2)
  have hcost : (36*(((2*(2^h))^(R.card+1))^2).size+258)*R.card≤
      (36*((height n h)^2).size+258)*n := Nat.mul_le_mul (by omega) hr
  exact ⟨τ,(r1.seq r2).mono (by dsimp only [timeBound]; omega),
    frame r2 p1.1 (by decide) (by decide),p2⟩

end Lax263307Proofs.NativeComponentDecision
