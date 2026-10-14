import Lax263307Proofs.NativeSelectedVertices
import Lax263307Proofs.NativeComponentDecision

namespace Lax263307Proofs.NativeComponentLoad

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeMasks NativeSignedArithmetic
open scoped NNRat

def prepare : Com := .seq (.assign "component.mask" (.get "separator.pieces" (.var "component.i")))
  (.seq (.assign "unpack.mask" (.var "component.mask"))
    (.seq NativeMaskUnpack.command NativeSelectedVertices.command))

theorem prepare_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ) (parts : List (Finset (Fin n))) (i : ℕ) (hi : i<parts.length)
    (hB : n+parts.length+3<B) (hm : 2^n<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧
      Prefix (encodeVector x) "near.costs" σ ∧ σ.vars "component.i"=i ∧
      Prefix (parts.map mask) "separator.pieces" σ ∧ n≤(σ.arrs "subset.bits").length ∧
      n≤(σ.arrs "restrict.vertices").length) prepare
      (fun _ τ => NativeRestrictionRead.Data G x parts[i] τ ∧ τ.vars "component.mask"=mask parts[i] ∧
        τ.vars "component.i"=i) (43*n+21) := by
  rintro σ ⟨hn,hgraph,hcosts,hidx,hparts,hbits,hlabels⟩
  have hget := hparts i (by simpa using hi)
  simp only [List.getElem_map] at hget
  let ν := σ.setVar "component.mask" (mask parts[i])
  have r0 : Run B (.assign "component.mask" (.get "separator.pieces" (.var "component.i"))) σ ν 3 :=
    Run.assign (evalB_get (by rw [evalB_var_iff]; exact ⟨hidx.symm,hidx ▸ (by omega)⟩)
      hget ((mask_bound _).trans hm))
  let μ := ν.setVar "unpack.mask" (mask parts[i])
  have r1 : Run B (.assign "unpack.mask" (.var "component.mask")) ν μ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨by simp [ν],by simp [ν]; exact (mask_bound _).trans hm⟩)
  obtain ⟨ρ,r2,p2⟩ := NativeMaskUnpack.command_spec B parts[i] (by omega) hm μ
    ⟨((r0.seq r1).frame_var _ (by decide)).trans hn,by simp [μ],
      by rw [RamFrames.run_array_length (r0.seq r1)]; exact hbits⟩
  have pre := r0.seq (r1.seq r2)
  obtain ⟨τ,r3,p3⟩ := NativeSelectedVertices.command_spec B n parts[i] (by omega) ρ
    ⟨(pre.frame_var _ (by decide)).trans hn,p2.1,
      by rw [RamFrames.run_array_length pre]; exact hlabels⟩
  have rr := r0.seq (r1.seq (r2.seq r3))
  refine ⟨τ,rr.mono (by omega),⟨p3.2.1,?_,?_,p3.2.2,p3.1.1⟩,?_,?_⟩
  · simpa only [Prefix,rr.frame_arr "search.graph" (by decide)] using hgraph
  · simpa only [Prefix,rr.frame_arr "near.costs" (by decide)] using hcosts
  · exact ((r1.seq (r2.seq r3)).frame_var _ (by decide)).trans (by simp [ν])
  · exact (rr.frame_var _ (by decide)).trans hidx

def command : Com := .seq prepare NativeComponentDecision.command

/-- Load one stored part, compute its canonical labels, exact cost,
heavy/light decision and recursive target without changing its list index. -/
theorem command_spec (n D k h : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → ℚ≥0) (hn : 0<n) (hD : 0<D) (hx : ∀ v,Bounded (2^h) (x v : ℚ))
    (w : ℕ) (hw : NativeComponentDecision.wordHeight n D k h≤w)
    (parts : List (Finset (Fin n))) (hparts : parts.length≤n+1) (i : ℕ) (hi : i<parts.length) :
    Spec (2^w) (fun σ => σ.vars "graph.n"=n ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" σ ∧
      Prefix (encodeVector (fun v => (x v : ℚ))) "near.costs" σ ∧ σ.vars "component.i"=i ∧
      Prefix (parts.map mask) "separator.pieces" σ ∧ n≤(σ.arrs "subset.bits").length ∧
      n≤(σ.arrs "restrict.vertices").length ∧ σ.vars "algorithm.D"=D ∧ σ.vars "conditioning.k"=k ∧
      3*n<(σ.arrs "lp.word").length ∧ 3*n≤(σ.arrs "sum.input").length) command
      (fun _ τ => NativeRestrictionRead.Data G (fun v => (x v : ℚ)) parts[i] τ ∧
        τ.vars "component.mask"=mask parts[i] ∧ τ.vars "component.i"=i ∧
        τ.vars "component.target"=ComputedRounding.target (1/(D : ℚ)) (∑ v∈parts[i],(x v : ℚ)) ∧
        τ.vars "component.active"=if (1/(D : ℚ))*k/(4*(n : ℚ))<(∑ v∈parts[i],(x v : ℚ)) then 1 else 0)
      (43*n+21+NativeComponentDecision.timeBound n h) := by
  have hwidth := hw
  dsimp only [NativeComponentDecision.wordHeight,NativeComponentResources.span] at hwidth
  have hB : n+parts.length+3<2^w := NativeUniformWordGuards.scalar _ w (by omega)
  have hm : 2^n<2^w := Nat.pow_lt_pow_right (by decide) (by omega)
  rintro σ ⟨horder,hgraph,hcosts,hidx,hpieces,hbits,hlabels,hDσ,hk,hlp,hsum⟩
  obtain ⟨ν,r1,p1⟩ := prepare_spec (2^w) G (fun v => (x v : ℚ)) parts i hi hB hm σ
    ⟨horder,hgraph,hcosts,hidx,hpieces,hbits,hlabels⟩
  obtain ⟨τ,r2,p2⟩ := NativeComponentDecision.command_spec n D k h G x hn hD hx w hw parts[i] ν
    ⟨p1.1,(r1.frame_var _ (by decide)).trans hDσ,(r1.frame_var _ (by decide)).trans hk,
      by rwa [RamFrames.run_array_length r1],by rwa [RamFrames.run_array_length r1]⟩
  exact ⟨τ,r1.seq r2,p2.1,(r2.frame_var _ (by decide)).trans p1.2.1,
    (r2.frame_var _ (by decide)).trans p1.2.2,p2.2⟩

end Lax263307Proofs.NativeComponentLoad
