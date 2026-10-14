import Lax263307Proofs.NativeConditioningFloor
import Lax263307Proofs.NativeSignedArithmetic
import Lax263307.ComputedSeparators
import Mathlib.Algebra.Order.Floor.Div

set_option maxHeartbeats 600000

namespace Lax263307Proofs.NativeLargeCapacity

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax263307 NativeSignedArithmetic

def numerator (b n r k : ℕ) : ℕ := b*(Nat.log2 (2*n)+1)*(2*r)*(2*r)*(3*k)
def denominator (n load : ℕ) : ℕ := load*n*n
def value (b n r load k : ℕ) : ℕ := (numerator b n r k+denominator n load-1)/denominator n load+1

theorem ceil_ratio (a b : ℕ) (hb : 0<b) : ⌈(a : ℚ)/b⌉₊=(a+b-1)/b := by
  have hbq : (0 : ℚ)<b := by exact_mod_cast hb
  change ⌈(a : ℚ)/b⌉₊=a⌈/⌉b
  apply Nat.le_antisymm
  · rw [Nat.ceil_le,div_le_iff₀ hbq]
    have hh : a≤b*(a⌈/⌉b) := (ceilDiv_le_iff_le_mul hb).mp le_rfl
    exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
  · rw [ceilDiv_le_iff_le_mul hb]
    have hh := (div_le_iff₀ hbq).mp (Nat.le_ceil ((a : ℚ)/b))
    norm_cast at hh
    simpa only [Nat.mul_comm] using hh

theorem exact_value (b n r load k : ℕ) (hn : 0<n) (hl : 0<load) :
    (ComputedSeparators.largeCapacity b n r load k : ℚ)=(value b n r load k : ℕ) := by
  have he : ComputedSeparators.ratio b n*(2*r : ℕ)^2/ComputedSeparators.scale n load k=
      (numerator b n r k : ℚ)/denominator n load := by
    simp only [ComputedSeparators.ratio,ComputedSeparators.scale,numerator,denominator,
      Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow,
      div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  have hd : 0<denominator n load := by unfold denominator; positivity
  change ((⌈ComputedSeparators.ratio b n*(2*r : ℕ)^2/ComputedSeparators.scale n load k⌉₊+1 : ℕ) : ℚ)=_
  rw [he,ceil_ratio _ _ hd]
  rfl

def resource (b n r load k : ℕ) : ℕ :=
  let L := Nat.log2 (2*n)+1
  b+n+r+load+k+L+2*n+2*r+3*k+b*L+b*L*(2*r)+b*L*(2*r)*(2*r)+
    2*numerator b n r k+load*n+2*denominator n load+20

def Input (b n r load k : ℕ) (σ : Env) : Prop :=
  σ.vars "class.B"=b ∧ σ.vars "graph.n"=n ∧ σ.vars "restrict.count"=r ∧
    σ.vars "algorithm.load"=load ∧ σ.vars "conditioning.k"=k

def products : Com := .seq
  (.assign "large.numerator" (.mul (.mul (.mul (.mul (.var "class.B") (.var "size.count"))
    (.mul (.lit 2) (.var "restrict.count"))) (.mul (.lit 2) (.var "restrict.count"))) (.mul (.lit 3) (.var "conditioning.k"))))
  (.assign "large.denominator" (.mul (.mul (.var "algorithm.load") (.var "graph.n")) (.var "graph.n")))

def finish : Com := .seq
  (.assign "large.value" (.add (.div (.sub (.add (.var "large.numerator") (.var "large.denominator")) (.lit 1))
    (.var "large.denominator")) (.lit 1)))
  (.seq (.assign "split.large.s" (.lit 0))
    (.seq (.assign "split.large.n" (.var "large.value")) (.assign "split.large.d" (.lit 1))))

def command : Com := .seq (.assign "size.value" (.mul (.lit 2) (.var "graph.n")))
  (.seq RamBitSize.word (.seq products finish))

/-- Compute the finite capacity used in the split network by exact
integer arithmetic, including the mathematical ceiling. -/
theorem command_spec (B b n r load k : ℕ) (hn : 0<n) (hl : 0<load)
    (hB : resource b n r load k<B) :
    Spec B (Input b n r load k) command
      (fun _ τ => Stored "split.large" (ComputedSeparators.largeCapacity b n r load k : ℚ) τ)
      (12*(2*n).size+60) := by
  have hguards := hB
  dsimp [resource] at hguards
  have hlog := NativeConditioningFloor.size_log (2*n) (by omega)
  have hprod : Spec B (fun σ => Input b n r load k σ ∧ σ.vars "size.count"=(2*n).size) products
      (fun _ τ => τ.vars "large.numerator"=numerator b n r k ∧ τ.vars "large.denominator"=denominator n load) 22 := by
    run_vcg
    all_goals simp_all [Input,numerator,denominator]
    all_goals omega
  have hvalueBound : value b n r load k<B := by
    dsimp [value]
    have hh := Nat.div_le_self (numerator b n r k+denominator n load-1) (denominator n load)
    omega
  have hfinish : Spec B (fun σ => σ.vars "large.numerator"=numerator b n r k ∧ σ.vars "large.denominator"=denominator n load)
      finish (fun _ τ => τ.vars "split.large.s"=0 ∧ τ.vars "split.large.n"=value b n r load k ∧ τ.vars "split.large.d"=1) 16 := by
    run_vcg
    all_goals simp_all [value]
    all_goals omega
  intro σ hc
  let ν := σ.setVar "size.value" (2*n)
  have r1 : Run B (.assign "size.value" (.mul (.lit 2) (.var "graph.n"))) σ ν 4 := Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (by omega))
      (by rw [evalB_var_iff]; exact ⟨hc.2.1.symm,hc.2.1 ▸ (by omega : n<B)⟩) (by change 2*n<B; omega))
  obtain ⟨μ,r2,p2⟩ := RamBitSize.word_spec B (2*n) (by omega) (by omega) ν (by simp [ν])
  have hcμ : Input b n r load k μ := by
    have rr := r1.seq r2
    simpa only [Input,rr.frame_var "class.B" (by decide),rr.frame_var "graph.n" (by decide),
      rr.frame_var "restrict.count" (by decide),rr.frame_var "algorithm.load" (by decide),
      rr.frame_var "conditioning.k" (by decide)] using hc
  obtain ⟨ξ,r3,p3⟩ := hprod μ ⟨hcμ,p2.2⟩
  obtain ⟨τ,r4,p4⟩ := hfinish ξ p3
  have hp4 : Stored "split.large" (value b n r load k : ℕ) τ := by
    simp [Stored,p4.1,p4.2.1,p4.2.2,fractionValue]
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by omega),by simpa only [exact_value b n r load k hn hl] using hp4⟩

end Lax263307Proofs.NativeLargeCapacity
