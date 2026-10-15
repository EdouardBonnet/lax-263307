import Lax263307Proofs.NativeNodeExecution
import Lax263307Proofs.NativeNodeResource
import Lax263307Proofs.NativePrecisionResources
import Lax263307Proofs.NativeExhaustiveResources

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeEntryResources

open Lax263307 AlgorithmParameters NativeCoreMachine

def buffers : List String := ["choose.table","subset.bits","catalog.mask","catalog.card","catalog.independent",
  "lp.input","moment.program","round.shape","round.center"]

def coefficient (cfg : Config) : ℕ := cfg.a+cfg.K+24*cfg.b+(4*cfg.a+2)+2000
def amount (cfg : Config) (R : ℕ) : ℕ := coefficient cfg*(R+1)^4

def shape (n k r N : ℕ) : ℕ := n*n+(n+1)*(k+1)+(n+1)*(r+3)+
  (2+3*((2+N*(n+4))*N)+3*((2+N*(n+4))+N))+3*(N*N)+3*N+n+k+r+N+100

theorem shape_bound (n k r N R : ℕ) (hn : n≤R) (hk : k≤R) (hr : r≤R) (hN : N≤R) :
    shape n k r N≤1000*(R+1)^4 := by
  have hs : shape n k r N≤shape R R R R := by unfold shape; gcongr
  apply hs.trans
  dsimp only [shape]
  nlinarith only [Nat.zero_le (R^4),Nat.zero_le (R^3),Nat.zero_le (R^2),Nat.zero_le R]

/-- Construct every actual entry/allocation guard from one root parameter
envelope and a fixed polynomial word-height/buffer budget. -/
theorem bounds (cfg : Config) (n D k fuel R w : ℕ) (extent : String → ℕ)
    (hK : 0<cfg.K) (hn : 0<n) (hD : 0<D) (hk : k≤n) (hf : fuel≤2*R+2)
    (hR : ParameterResources.resource cfg.a cfg.K cfg.b n D≤R)
    (hw : amount cfg R≤w) (hroom : ∀ a∈buffers,amount cfg R≤extent a) :
    NativeNodeExecution.Bounds w D k fuel n cfg extent := by
  let r := level cfg.a cfg.K cfg.b n D
  let N := MomentLP.dimension n r
  let U := R+1
  have hnR : n≤R := by dsimp only [ParameterResources.resource] at hR; omega
  have hkR : k≤R := hk.trans hnR
  have hrR : r≤R := by dsimp only [r,ParameterResources.resource] at hR ⊢; omega
  have hNR : N≤R := by dsimp only [N,r,ParameterResources.resource] at hR ⊢; omega
  have hcR : cutoff cfg.a cfg.K cfg.b n D≤R := by
    have hp : (n+1)^cutoff cfg.a cfg.K cfg.b n D≤R := by dsimp only [ParameterResources.resource] at hR; omega
    exact Nat.lt_two_pow_self.le.trans ((Nat.pow_le_pow_left (by omega : 2≤n+1) _).trans hp)
  have hU : 1≤U := by dsimp [U]; omega
  have h24 : U^2≤U^4 := Nat.pow_le_pow_right hU (by decide)
  have hU4 : U≤U^4 := le_self_pow hU (by decide)
  have hc : 2000≤coefficient cfg := by dsimp only [coefficient]; omega
  have hshape := (shape_bound n k r N R hnR hkR hrR hNR).trans
    (Nat.mul_le_mul_right ((R+1)^4) (show 1000≤coefficient cfg by omega))
  have hshapeWord : shape n k r N<2^w := hshape.trans_lt (hw.trans_lt Nat.lt_two_pow_self)
  have hnw : n<w := by
    have ha : R+1≤amount cfg R := hU4.trans (Nat.le_mul_of_pos_left _ (by omega : 0<coefficient cfg))
    have ha' := ha.trans hw
    omega
  have hm : 2^n<2^w := Nat.pow_lt_pow_right (by decide) hnw
  have hg := NativeNodeResource.guard_bound cfg.a cfg.K cfg.b n D hK hn
  have hg4 : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D≤
      (cfg.a+cfg.K+24*cfg.b+(4*cfg.a+2)+50)*U^4 :=
    hg.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.add_le_add_right hR 1) 2).trans h24))
  have hp := NativePrecisionResources.actual_guard cfg.a cfg.K cfg.b n D hK hn hD
  have hp4 : NativeNodePrecision.guard n D N (floorDenominator cfg.a cfg.K cfg.b n D) r≤400*U^4 :=
    hp.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.add_le_add_right hR 1) 2).trans h24))
  have hguard : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+n+k+cutoff cfg.a cfg.K cfg.b n D+fuel+29≤amount cfg R := by
    dsimp only [amount,coefficient,U] at *
    nlinarith only [hg4,hnR,hkR,hcR,hf,hU4,Nat.one_le_pow 4 (R+1) (by omega)]
  have hparams : NativeNodeParameters.guard cfg.a cfg.K cfg.b n D+k+cfg.b+5≤amount cfg R := by
    have hbR : cfg.b≤R := by
      have hload : load cfg.b n D≤R := by dsimp only [ParameterResources.resource] at hR; omega
      dsimp only [load] at hload
      have hlog : 1≤logarithm n := by dsimp only [logarithm]; omega
      nlinarith only [hload,Nat.mul_le_mul hD hlog]
    dsimp only [amount,coefficient,U] at *
    nlinarith only [hg4,hkR,hbR,hU4,Nat.one_le_pow 4 (R+1) (by omega)]
  have hprec : NativeNodePrecision.guard n D N (floorDenominator cfg.a cfg.K cfg.b n D) r≤amount cfg R :=
    hp4.trans (Nat.mul_le_mul_right _ (show 400≤coefficient cfg by omega))
  have hlen : NativeMomentInput.length n r=2+3*((2+N*(n+4))*N)+3*((2+N*(n+4))+N) := by
    rw [NativeMomentInput.length,NativeMomentInput.row_count_eq]
  have room (a : String) (ha : a∈buffers) : shape n k r N≤extent a := hshape.trans (hroom a ha)
  dsimp only [shape] at hshapeWord room
  refine ⟨hguard.trans_lt (hw.trans_lt Nat.lt_two_pow_self),?_,hm,
    NativeExhaustiveResources.table_words _ n k hm,hK,hparams.trans_lt (hw.trans_lt Nat.lt_two_pow_self),?_,
    hprec.trans_lt (hw.trans_lt Nat.lt_two_pow_self),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · omega
  · change n*n+(n+1)*(r+3)+NativeMomentInput.length n r+n+k+r+N+20<2^w
    rw [hlen]; omega
  · change 3*(N*N)+3*N+20<2^w; omega
  · have h := room "choose.table" (by simp [buffers]); omega
  · have h := room "choose.table" (by simp [buffers]); change (n+1)*(r+3)≤extent "choose.table"; omega
  · have h := room "subset.bits" (by simp [buffers]); omega
  · have h := room "catalog.mask" (by simp [buffers]); change N≤extent "catalog.mask"; omega
  · have h := room "catalog.card" (by simp [buffers]); change N≤extent "catalog.card"; omega
  · have h := room "catalog.independent" (by simp [buffers]); change N≤extent "catalog.independent"; omega
  · have h := room "lp.input" (by simp [buffers]); change NativeMomentInput.length n r≤extent "lp.input"; rw [hlen]; omega
  · have h := room "moment.program" (by simp [buffers]); change NativeMomentInput.length n r≤extent "moment.program"; rw [hlen]; omega
  · have h := room "lp.input" (by simp [buffers]); change 3*(N*N)+3*N≤extent "lp.input"; omega
  · have h := room "round.shape" (by simp [buffers]); change 3*(N*N)≤extent "round.shape"; omega
  · have h := room "round.center" (by simp [buffers]); change 3*N≤extent "round.center"; omega

end Lax263307Proofs.NativeEntryResources
