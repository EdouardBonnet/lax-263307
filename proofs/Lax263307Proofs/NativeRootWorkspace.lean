import Lax263307Proofs.NativeSelectedBudget
import Lax263307Proofs.NativeSourceFrame

set_option maxHeartbeats 250000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeRootWorkspace

open Lax263307 AlgorithmParameters NativeCoreMachine NativeSelectedRounds

def stride (W : ℕ) : ℕ := 2*(W+1)
def frameLength (cfg : Config) (W : ℕ) : ℕ := stride W*(frameArrays cfg).length+(frameScalars cfg).length
def capacity (cfg : Config) (rootN W : ℕ) : ℕ := RecursionDepth.depth rootN*frameLength cfg W

def extent (cfg : Config) (rootN W originalN : ℕ) (a : String) : ℕ :=
  if a="recursion.frames" then capacity cfg rootN W
  else if a="image.output" then originalN
  else if a="weighted.output" then originalN else stride W

def hostHeight (cfg : Config) (W : ℕ) : ℕ := W+
  NativeNearResources.wordHeight cfg W W (stride W) ((2*W+2)*frameLength cfg W)+
  NativeRoundedResources.wordHeight cfg.rounded W W W+100

theorem ordinary (cfg : Config) (rootN W originalN : ℕ) (a : String)
    (ha : a∉["recursion.frames","image.output","weighted.output"]) :
    extent cfg rootN W originalN a=stride W := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at ha
  simp only [extent,if_neg ha.1,if_neg ha.2.1,if_neg ha.2.2]

theorem buffer_room (cfg : Config) (rootN W originalN amount : ℕ) (buffers : List String)
    (clean : List.Disjoint buffers ["recursion.frames","image.output","weighted.output"])
    (hamount : amount ≤ W) : ∀ a∈buffers,amount ≤ extent cfg rootN W originalN a := by
  intro a ha
  rw [ordinary cfg rootN W originalN a (List.disjoint_left.mp clean ha)]
  dsimp only [stride]
  omega

theorem frame_extents (cfg : Config) (rootN W originalN : ℕ) :
    ∀ a∈frameArrays cfg,extent cfg rootN W originalN a=stride W := by
  intro a ha
  apply ordinary
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  rintro (rfl|rfl|rfl)
  · have h := ha
    simp only [frameArrays,List.mem_filter,List.mem_dedup,bne_iff_ne] at h
    exact h.2 rfl
  · exact NativeSourceFrame.array_unsaved cfg _ (by simp) ha
  · exact NativeSourceFrame.array_unsaved cfg _ (by simp) ha

theorem frame_positive (cfg : Config) (W : ℕ) : 0<frameLength cfg W := by
  have h : 0<(frameScalars cfg).length := List.length_pos_of_mem (phase_saved cfg)
  dsimp only [frameLength]
  omega

/-- One root allocation and host height satisfy every oracle/search-round
guard at every eligible large node. The budget demand is a fixed polynomial
and contains no execution or recursion hypothesis. -/
theorem bounds {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (c rootN originalN R W w : ℕ)
    (hK : 0<cfg.K) (hb : 0<cfg.b) (hroot : rootN ≤ R)
    (budget : NativeSelectedBudget.demand cfg p q c R ≤ W) (host : hostHeight cfg W ≤ w)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D k fuel : ℕ) (front : List ℕ)
    (hn : 0<n) (hD : 0<D) (hk : k ≤ n) (hf : fuel ≤ 2*R+2)
    (resource : ParameterResources.resource cfg.a cfg.K cfg.b n D ≤ R)
    (stack : front.length+frameLength cfg W ≤ capacity cfg rootN W) :
    NativeSelectedRounds.Bounds cfg p q G D k fuel (stride W) W c R w (extent cfg rootN W originalN) front := by
  have hdem := budget
  dsimp only [NativeSelectedBudget.demand] at hdem
  have hR : R ≤ W := by omega
  have hcert : H p R ≤ W := by change NativeSelectedLP.certificateHeight p R ≤ W; omega
  have hroundH : NativeOraclePrecision.roundedHeight p.width R ≤ W := by omega
  have hhost : W ≤ w := by dsimp only [hostHeight] at host; omega
  have hnR : n ≤ R := by dsimp only [ParameterResources.resource] at resource; omega
  have hkR : k ≤ R := hk.trans hnR
  have hrR : level cfg n D ≤ R := by dsimp only [ParameterResources.resource,NativeSelectedRounds.level] at resource ⊢; omega
  have hDR : D ≤ R := by dsimp only [ParameterResources.resource] at resource; omega
  have hpR : sparsity cfg.a cfg.K cfg.b n D ≤ R := by dsimp only [ParameterResources.resource] at resource; omega
  have hNR : N cfg n D ≤ R := by dsimp only [ParameterResources.resource,N,NativeSelectedRounds.level] at resource ⊢; omega
  have hlR : load cfg.b n D ≤ R := by dsimp only [ParameterResources.resource] at resource; omega
  have hiR : limit cfg n D ≤ R := by dsimp only [ParameterResources.resource,limit] at resource ⊢; omega
  have hp : 0<sparsity cfg.a cfg.K cfg.b n D := by
    unfold sparsity targetThreshold
    exact Nat.mul_pos (by decide) (Nat.mul_pos hK (Nat.pow_pos (by omega)))
  have hfloor : 0<F cfg n D := by
    apply Nat.pow_pos
    unfold floorDenominator
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hn) hp) (by omega)
  have hdim : 2 ≤ N cfg n D := CoordinateCatalog.catalog_two n (level cfg n D) hn
  have hNpos : 0<N cfg n D := lt_of_lt_of_le (by decide) hdim
  have hFR : F cfg n D ≤ R := by
    have hrad : radiusDenominator cfg.a cfg.K cfg.b n D ≤ R := by dsimp only [ParameterResources.resource] at resource; omega
    have hfactor : 0<256*N cfg n D*n^2*D^2 :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hNpos) (Nat.pow_pos hn)) (Nat.pow_pos hD)
    have h := Nat.le_mul_of_pos_left (F cfg n D) hfactor
    apply h.trans
    exact hrad
  have hdepth : RecursionDepth.depth rootN ≤ 2*W+2 := by
    have h := RecursionDepth.logarithmic_bound rootN
    have hl : Nat.log2 rootN ≤ rootN := Nat.log2_le_self rootN
    omega
  have hcursor : front.length ≤ (2*W+2)*frameLength cfg W := by
    have hcap := Nat.mul_le_mul_right (frameLength cfg W) hdepth
    dsimp only [capacity] at stack
    omega
  have hnearWord : NativeNearResources.wordHeight cfg R (H p R) (stride W) front.length ≤ w := by
    have hm : NativeNearResources.wordHeight cfg R (H p R) (stride W) front.length ≤ 
        NativeNearResources.wordHeight cfg W W (stride W) ((2*W+2)*frameLength cfg W) := by
      dsimp only [NativeNearResources.wordHeight]
      gcongr
    exact hm.trans (by dsimp only [hostHeight] at host; omega)
  have hnear := NativeNearResources.bounds cfg n (level cfg n D) D k (sparsity cfg.a cfg.K cfg.b n D)
    fuel (stride W) (H p R) R w (extent cfg rootN W originalN) front hn hD hp hnR hrR hDR hkR hpR hNR hf
    hnearWord (frame_extents cfg rootN W originalN) (by simpa [extent,frameLength,Nat.add_assoc] using stack)
    (buffer_room cfg rootN W originalN (NativeNearResources.space R) NativeNearResources.buffers (by simp [List.disjoint_left,NativeNearResources.buffers]) (by omega))
  have hproj := NativeProjectionResources.bounds G D k (level cfg n D) (F cfg n D) R w (NativeSelectedLP.oracleTime p R)
    (extent cfg rootN W originalN) hn hD hfloor hnR hDR hFR hNR
    ((by omega : NativeProjectionResources.wordHeight R ≤ W).trans hhost)
    (buffer_room cfg rootN W originalN (NativeProjectionResources.space R (NativeSelectedLP.oracleTime p R)) NativeProjectionResources.buffers (by simp [List.disjoint_left,NativeProjectionResources.buffers]) (by omega))
  have hheight := NativeSelectedBudget.cost_height p R
  have flowHeight := NativeFlowBudget.height_bound cfg.b n (load cfg.b n D) k (2*H p R) R
    (NativePolynomialBudget.heightPolynomial p.width) hnR hlR hkR hheight
  have flowWidth := NativeFlowBudget.width_bound cfg.b n (flowH cfg p n D k R) R
    (NativePolynomialBudget.heightPolynomial p.width) q.width q.time q.output q.code hnR flowHeight
  have flowSpace := NativeFlowBudget.space_bound cfg.b n (flowH cfg p n D k R) R
    (NativePolynomialBudget.heightPolynomial p.width) q.time hnR flowHeight
  have roundedHost : NativeRoundedResources.wordHeight cfg.rounded W R
      (NativeOraclePrecision.roundedHeight p.width R) ≤ w := by
    have hm : NativeRoundedResources.wordHeight cfg.rounded W R
        (NativeOraclePrecision.roundedHeight p.width R) ≤ NativeRoundedResources.wordHeight cfg.rounded W W W := by
      dsimp only [NativeRoundedResources.wordHeight]; gcongr
    exact hm.trans (by dsimp only [hostHeight] at host; omega)
  refine ⟨hnR,hkR,hrR,hDR,hFR,hNR,hiR,hproj,hnear,(by omega),?_,?_,?_,?_,?_,roundedHost,?_⟩
  · have hm : NativeCutResources.wordExponent (N cfg n D) (2*H p R+1) ≤ NativeCutResources.wordExponent R (2*H p R+1) := by
      dsimp only [NativeCutResources.wordExponent]; gcongr
    have hfar : NativeCutResources.wordExponent R (2*H p R+1)+4 ≤ W := by
      change NativeCutResources.wordExponent R (2*NativeSelectedLP.certificateHeight p R+1)+4 ≤ W
      omega
    exact (Nat.add_le_add_right hm 4).trans (hfar.trans hhost)
  · rw [ordinary cfg rootN W originalN "vm.input" (by decide)]
    dsimp only [stride]
    omega
  · exact flowWidth.trans (by omega)
  · apply buffer_room cfg rootN W originalN _ NativeSeparatorContext.workspace (by simp [List.disjoint_left,NativeSeparatorContext.workspace])
    exact flowSpace.trans (by omega)
  · have hspace : NativeRoundedResources.space c R (NativeOraclePrecision.roundedHeight p.width R) ≤ W := by omega
    dsimp only [NativeRoundedResources.space] at hspace
    omega
  · exact buffer_room cfg rootN W originalN _ NativeRoundedResources.buffers (by simp [List.disjoint_left,NativeRoundedResources.buffers]) (by omega)

end Lax263307Proofs.NativeRootWorkspace
