import Lax263307Proofs.NativeNodeAliases
import Lax263307Proofs.NativeMomentSetup
import Lax263307Proofs.NativeLargeSetup

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeLargeNode

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 AlgorithmParameters MomentLP RoundedOracleSearch

def command (a K b : ℕ) : Com := .seq (NativeNodeParameters.command a K b)
  (.seq (NativeNodeAliases.command b) (.seq NativeMomentSetup.command NativeLargeSetup.command))

def cost (a n r : ℕ) : ℕ := 12*n.size+12*(2*n).size+12*(4*a+2)+76+
  NativeMomentSetup.cost n r+NativeLargeSetup.timeBound n r

theorem aliases_frame {B a K b n D k t : ℕ} {σ τ : Env}
    (rr : Run B (.seq NativeMomentSetup.command NativeLargeSetup.command) σ τ t)
    (hs : NativeNodeAliases.Output a K b n D k σ) : NativeNodeAliases.Output a K b n D k τ :=
  ⟨(rr.frame_var "row.k" (by decide)).trans hs.1,
    (rr.frame_var "conditioning.k" (by decide)).trans hs.2.1,
    (rr.frame_var "conditioning.p" (by decide)).trans hs.2.2.1,
    (rr.frame_var "algorithm.load" (by decide)).trans hs.2.2.2.1,
    (rr.frame_var "algorithm.D" (by decide)).trans hs.2.2.2.2.1,
    (rr.frame_var "class.B" (by decide)).trans hs.2.2.2.2.2⟩

/-- The large-node setup program computes every parameter and builds
every initial LP/state buffer from the encoded graph and runtime target.
Only class constants occur as source-program parameters. -/
def Input {n : ℕ} (B a K b D k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (σ : Env) : Prop :=
  let r := level a K b n D
  let N := dimension n r
  σ.vars "graph.n"=n ∧ σ.vars "node.D"=D ∧ σ.vars "node.k"=k ∧
      Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧ NativeArrayBounds.Bounded B σ ∧
      (n+1)*(r+3)≤(σ.arrs "choose.table").length ∧ n≤(σ.arrs "subset.bits").length ∧
      N≤(σ.arrs "catalog.mask").length ∧ N≤(σ.arrs "catalog.card").length ∧ N≤(σ.arrs "catalog.independent").length ∧
      NativeMomentInput.length n r≤(σ.arrs "lp.input").length ∧
      NativeMomentInput.length n r≤(σ.arrs "moment.program").length ∧
      3*(N*N)+3*N≤(σ.arrs "lp.input").length ∧ 3*(N*N)≤(σ.arrs "round.shape").length ∧
      3*N≤(σ.arrs "round.center").length

def Output {n : ℕ} (a K b D k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (τ : Env) : Prop :=
  let r := level a K b n D
  let N := dimension n r
  NativeNodeAliases.Output a K b n D k τ ∧ NativeMomentFamily.Data G k r τ ∧
        Prefix (encodeProgram (MomentLP.program G k r)) "moment.program" τ ∧
        τ.vars "node.programLength"=NativeMomentInput.length n r ∧
        NativeNodePrecision.Output n D N (floorDenominator a K b n D) r τ ∧
        Prefix (NativeRoundedQuery.shape ((1,0) : State N)) "round.shape" τ ∧
        Prefix (NativeRoundedQuery.center ((1,0) : State N)) "round.center" τ ∧ τ.vars "round.i"=0

theorem command_spec {n : ℕ} (B a K b D k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 0<n) (hK : 0<K)
    (hparams : NativeNodeParameters.guard a K b n D+k+b+5<B)
    (hsetup : NativeMomentSetup.guardBound n k (level a K b n D)<B) (hm : 2^n<B)
    (hprec : NativeNodePrecision.guard n D (dimension n (level a K b n D))
      (floorDenominator a K b n D) (level a K b n D)<B)
    (hround : 3*(dimension n (level a K b n D)*dimension n (level a K b n D))+
      3*dimension n (level a K b n D)+20<B) :
    let r := level a K b n D
    let N := dimension n r
    Spec B (Input B a K b D k G) (command a K b) (fun _ τ => Output a K b D k G τ)
      (cost a n r) := by
  dsimp only
  rintro σ ⟨horder,hD,hk,hgraph,hbounded,htable,hbits,hmask,hcard,hind,hinput,hcache,hroundinput,hshape,hcenter⟩
  obtain ⟨ν,r1,p1⟩ := NativeNodeParameters.command_spec B a K b n D hn (by omega) σ ⟨horder,hD⟩
  have hkν := (r1.frame_var "node.k" (by simp [NativeNodeParameters.command,NativeNodeParameters.setup,
    NativeNodeParameters.finish,Com.wvars,NativeLogarithms.command,NativeLogarithms.small,NativeLogarithms.large,
    RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,NativeNaturalPower.command,NativeNaturalPower.step])).trans hk
  obtain ⟨μ,r2,p2⟩ := NativeNodeAliases.command_spec B a K b n D k hparams ν ⟨p1,hkν⟩
  have hnμ := (r2.frame_var "graph.n" (by simp [NativeNodeAliases.command,Com.wvars])).trans p1.1.1
  have hDμ := (r2.frame_var "node.D" (by simp [NativeNodeAliases.command,Com.wvars])).trans p1.1.2.1
  have hrμ := (r2.frame_var "moment.r" (by simp [NativeNodeAliases.command,Com.wvars])).trans p1.2.2.2.2.1
  have hbμ := (r2.frame_var "node.floorDen" (by simp [NativeNodeAliases.command,Com.wvars])).trans p1.2.2.2.2.2.2
  obtain ⟨ρ,r3,p3⟩ := NativeMomentSetup.command_spec B G k (level a K b n D) hsetup hm μ
    ⟨hnμ,p2.1,hrμ,
      by simpa only [Prefix,(r1.seq r2).frame_arr "search.graph" (by simp [NativeNodeParameters.command,
        NativeNodeParameters.setup,NativeNodeParameters.finish,NativeLogarithms.command,NativeLogarithms.small,
        NativeLogarithms.large,RamBitSize.word,RamBitSize.wordLoop,RamBitSize.wordStep,NativeNaturalPower.command,
        NativeNaturalPower.step,NativeNodeAliases.command,Com.warrs])] using hgraph,
      by rw [RamFrames.run_array_length (r1.seq r2)]; exact htable,
      by rw [RamFrames.run_array_length (r1.seq r2)]; exact hbits,
      by rw [RamFrames.run_array_length (r1.seq r2)]; exact hmask,
      by rw [RamFrames.run_array_length (r1.seq r2)]; exact hcard,
      by rw [RamFrames.run_array_length (r1.seq r2)]; exact hind⟩
  have hc : NativeNodePrecision.Context n D (dimension n (level a K b n D))
      (floorDenominator a K b n D) (level a K b n D) ρ :=
    ⟨p3.1.1.1,(r3.frame_var "node.D" (by decide)).trans hDμ,p3.1.1.2.1,
      (r3.frame_var "node.floorDen" (by decide)).trans hbμ,p3.1.2.2.2⟩
  have hfloor : 1≤floorDenominator a K b n D := by
    change 0<floorDenominator a K b n D
    unfold floorDenominator sparsity targetThreshold
    positivity
  obtain ⟨τ,r4,p4⟩ := NativeLargeSetup.command_spec B G k (level a K b n D) D
    (floorDenominator a K b n D) hfloor (by dsimp only [NativeMomentSetup.guardBound,NativeMomentSetup.N] at hsetup; omega)
    hm hprec hround ρ
    ⟨p3,hc,NativeArrayBounds.run (r1.seq (r2.seq r3)) hbounded,
      by rw [RamFrames.run_array_length (r1.seq (r2.seq r3))]; exact hinput,
      by rw [RamFrames.run_array_length (r1.seq (r2.seq r3))]; exact hcache,
      by rw [RamFrames.run_array_length (r1.seq (r2.seq r3))]; exact hroundinput,
      by rw [RamFrames.run_array_length (r1.seq (r2.seq r3))]; exact hshape,
      by rw [RamFrames.run_array_length (r1.seq (r2.seq r3))]; exact hcenter⟩
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by dsimp only [cost]; omega),
    aliases_frame (r3.seq r4) p2,p4⟩

end Lax263307Proofs.NativeLargeNode
