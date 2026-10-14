import Lax263307Proofs.NativeSeparatorContext
import Lax263307Proofs.NativeFlowQueryResources
import Lax263307Proofs.NativeUniformWordGuards

set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

namespace Lax263307Proofs.NativeUniformFlow

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax263307 ComputedSeparators NativeSignedArithmetic
open NativeSeparatorContext NativeFlowQueryResources NativeUniformWordGuards
open scoped NNRat

def shape (n : ℕ) : ℕ := 8*n*n+6*n+40

def wordHeight (n H : ℕ) (p : Lax808846.Ram.Program) (wp tp op : Polynomial ℕ) : ℕ :=
  let S := sizeBound n H
  2*wp.eval (S+1)+H+shape n+S+tp.eval S+op.eval S+RamVirtualConstants.allowance p+20

def spaceBound (n H : ℕ) (tp : Polynomial ℕ) : ℕ :=
  NativeSplitInput.wordLength n+tp.eval (sizeBound n H)+n+2

def callbackTime (n H : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ) (tp : Polynomial ℕ) : ℕ :=
  43*n+12*(2*n).size+78+NativeSplitOracle.cost n p coeff (tp.eval (sizeBound n H)) (sizeBound n H)+59*n+42*n+42

theorem cost_mono (r n s S t T : ℕ) (p : Lax808846.Ram.Program) (coeff : List ℕ)
    (hr : r≤n) (hs : s≤S) (ht : t≤T) : NativeSplitOracle.cost r p coeff t s≤NativeSplitOracle.cost n p coeff T S := by
  have hlen : NativeSplitInput.wordLength r≤NativeSplitInput.wordLength n := by
    dsimp [NativeSplitInput.wordLength]
    nlinarith only [hr,Nat.mul_le_mul hr hr]
  dsimp only [NativeSplitOracle.cost]
  gcongr

/-- A single fixed flow-call command works for every induced remaining
set. All its arithmetic, solver, and output-length guards follow from
one uniform word bound; one common workspace suffices. -/
theorem exists_callback (f : List ℕ → List ℕ) (hf : RamPolytime f) :
    ∃ (p : Lax808846.Ram.Program) (wp tp op : Polynomial ℕ) (coeff : List ℕ),
    (∀ z : ℕ,RamPolynomial.value coeff z=wp.eval z) ∧
    ∀ (b n load k h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → ℚ≥0),
    0<n → 0<load → (∀ v,Bounded (2^h) (x v : ℚ)) →
    let H := NativeLargeResources.heightExponent b n load k h
    ∀ w : ℕ,wordHeight n H p wp tp op≤w → ∀ R : Finset (Fin n),
    Spec (2^w) (fun σ => Context G x b load k (spaceBound n H tp) σ ∧ σ.vars "separator.remaining"=NativeMasks.mask R)
      (callback p coeff) (fun _ τ => Context G x b load k (spaceBound n H tp) τ ∧
        τ.vars "cut.left"=NativeMasks.mask (ComputedSeparators.step f G x b load k R).1 ∧
        τ.vars "cut.right"=NativeMasks.mask (ComputedSeparators.step f G x b load k R).2)
      (callbackTime n H p coeff tp) := by
  obtain ⟨p,wp,tp,op,coeff,hcoeff,_,hcall⟩ := NativeFlowCut.exists_invocation f hf
  refine ⟨p,wp,tp,op,coeff,hcoeff,?_⟩
  intro b n load k h G _ x hn hl hx
  dsimp only
  let H := NativeLargeResources.heightExponent b n load k h
  let S := sizeBound n H
  let U := wp.eval (S+1)
  let T := tp.eval S
  let O := op.eval S
  let A := RamVirtualConstants.allowance p
  intro w hwidth R
  have hw : 2*U+H+shape n+S+T+O+A+20≤w := hwidth
  have hHn : n+30≤H := by dsimp [H,NativeLargeResources.heightExponent]; omega
  have hL : 3*n+5≤shape n := by dsimp [shape]; nlinarith only []
  have hxH : ∀ v,Bounded (2^H) (x v : ℚ) := fun v => NativeLargeResources.input_height b n load k h _ (hx v)
  let large := largeCapacity b n R.card load k
  let q := NativeSplitOracle.query G x R large
  have hlH : Bounded (2^H) (large : ℚ) := NativeLargeResources.capacity_height b n load k h R hn hl
  have hs : bitSize q≤S := query_size n H G x R large hxH hlH
  have hu : wp.eval (bitSize q+1)≤U := eval_mono wp (Nat.add_le_add_right hs 1)
  have hu0 : wp.eval (bitSize q)≤U := eval_mono wp (by omega)
  have ht : tp.eval (bitSize q)≤T := eval_mono tp hs
  have ho : op.eval (bitSize q)≤O := eval_mono op hs
  have hm : 2^H<2^w := by
    simpa only [Nat.add_zero] using power_add H 0 w (by omega) (by omega)
  have hnword : 2^n<2^w := (Nat.pow_le_pow_right (by decide) (by omega : n≤H)).trans_lt hm
  have hshape : 8*n*n+6*n+2^H+40<2^w := by
    simpa only [shape,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using power_add H (shape n) w (by omega) (by omega)
  have hr : NativeLargeCapacity.resource b n R.card load k<2^w :=
    scalar _ w ((NativeLargeResources.resource_le_height b n load k h R).trans (by omega))
  have hR := NativeMaskUnpack.card_bound R
  have hlen : NativeSplitInput.wordLength R.card≤NativeSplitInput.wordLength n := by
    dsimp [NativeSplitInput.wordLength]
    nlinarith only [hR,Nat.mul_le_mul hR hR]
  have hspaceN : n≤spaceBound n H tp := by dsimp [spaceBound]; omega
  have hspaceQ : NativeSplitInput.wordLength R.card<spaceBound n H tp := by dsimp [spaceBound]; omega
  have hspaceT : tp.eval (bitSize q)<spaceBound n H tp := by dsimp [spaceBound]; change _<NativeSplitInput.wordLength n+T+n+2; omega
  obtain ⟨_,hquery⟩ := hcall n G x R large
  have hgSize : bitSize q+1<2^w := scalar _ w (by omega)
  have hgPoly : wp.eval (bitSize q+1)<2^w := scalar _ w (by omega)
  have hgVirtual : 2*(2^wp.eval (bitSize q))^2+3<2^w := virtual _ w (by omega)
  have hgTime : tp.eval (bitSize q)+1<2^w := scalar _ w (by omega)
  have hgAllowance : RamVirtualConstants.allowance p<2^w := scalar _ w (by change A≤w; omega)
  have hgOutput : op.eval (bitSize q)+2*n+4<2^w := scalar _ w (by omega)
  have hc := hquery (2^w) (2^H) Nat.one_le_two_pow hshape hxH hlH
    hgSize hgPoly hgVirtual hgTime hgAllowance hgOutput hnword
  rintro σ ⟨hd,hremaining⟩
  obtain ⟨ν,r1,p1⟩ := NativeFlowPrepare.command_spec (2^w) b n load k G (fun v => (x v : ℚ)) R hn hl
    (scalar _ w (by omega)) hnword hr σ
    ⟨hd.graph,hd.costs,hd.order,hremaining,hd.classB,hd.load,hd.target,
      hspaceN.trans (hd.room "subset.bits" (by simp [workspace])),
      hspaceN.trans (hd.room "restrict.vertices" (by simp [workspace]))⟩
  have hroom (a : String) (ha : a∈workspace) : spaceBound n H tp≤(ν.arrs a).length := by
    rw [RamFrames.run_array_length r1]; exact hd.room a ha
  obtain ⟨τ,r2,p2⟩ := hc ν
    ⟨p1.1,p1.2,hspaceQ.trans_le (hroom "lp.word" (by simp [workspace])),
      by simpa only [q,NativeSplitOracle.query,NativeSplitInput.input_length] using
        hspaceQ.trans_le (hroom "vm.input" (by simp [workspace])),
      hspaceT.trans_le (hroom "vm.addresses" (by simp [workspace])),
      hspaceT.trans_le (hroom "vm.values" (by simp [workspace])),
      hspaceT.trans_le (hroom "vm.output" (by simp [workspace])),
      hspaceN.trans (hroom "subset.bits" (by simp [workspace]))⟩
  have hcost : NativeSplitOracle.cost R.card p coeff (tp.eval (bitSize q)) (bitSize q)+59*R.card+42*n+42≤
      NativeSplitOracle.cost n p coeff T S+59*n+42*n+42 := by
    have hh := cost_mono R.card n (bitSize q) S (tp.eval (bitSize q)) T p coeff hR hs ht
    omega
  have rr := r1.seq r2
  refine ⟨τ,rr.mono (by
      simpa only [callbackTime,Nat.add_assoc] using Nat.add_le_add_left hcost (43*n+12*(2*n).size+78)),
    callback_frame rr hd,?_,?_⟩
  · simpa only [NativeFlowCut.step_eq,q,large] using p2.2.1
  · simpa only [NativeFlowCut.step_eq,q,large] using p2.2.2

end Lax263307Proofs.NativeUniformFlow
