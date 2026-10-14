import Lax263307Proofs.NativeRecursionFrame
import Lax263307Proofs.NativeChildActivate

namespace Lax263307Proofs.NativeChildCall

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

theorem save_variable (arrays scalars : List String) (s : String)
    (hs : s∉["stack.i","stack.copy.length","stack.words"]) :
    s∉(NativeRecursionFrame.save arrays scalars).wvars := by
  have hw : s≠"stack.words" := fun h => hs (by simp [h])
  simpa only [NativeRecursionFrame.save,Com.wvars,List.mem_append,not_or] using
    And.intro (NativeRecursionFrame.buffers_variable arrays s hs) (NativeFrameScalars.save_variable scalars s hw)

theorem save_array (arrays scalars : List String) (a : String) (ha : a≠"recursion.frames") :
    a∉(NativeRecursionFrame.save arrays scalars).warrs := by
  have hs : a∉(NativeFrameScalars.save scalars).warrs := by
    induction scalars with
    | nil => simp [NativeFrameScalars.save,Com.warrs]
    | cons s ss ih => simp [NativeFrameScalars.save,RamWordBuffer.append,Com.warrs,ha,ih]
  simpa only [NativeRecursionFrame.save,Com.warrs,List.mem_append,not_or] using
    And.intro (NativeFrameBuffers.array_frame arrays a ha) hs

def enter (entry : ℕ) : Com := .seq (.assign "node.k" (.var "component.target"))
  (.seq (.assign "recursion.fuel" (.sub (.var "recursion.fuel") (.lit 1)))
    (.assign "machine.phase" (.lit entry)))

theorem enter_spec (B target fuel entry : ℕ) (hB : target+fuel+entry+3<B) :
    Spec B (fun σ => σ.vars "component.target"=target ∧ σ.vars "recursion.fuel"=fuel+1) (enter entry)
      (fun _ τ => τ.vars "node.k"=target ∧ τ.vars "recursion.fuel"=fuel ∧ τ.vars "machine.phase"=entry) 8 := by
  intro σ hs
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

def command (arrays scalars : List String) (entry continuation : ℕ) : Com :=
  .seq (.assign "machine.phase" (.lit continuation))
    (.seq (NativeRecursionFrame.save arrays scalars) (.seq NativeChildActivate.command (enter entry)))

/-- Save the parent with its child-reply continuation, activate the
prepared child graph, pass its target, and reduce the recursion fuel. -/
theorem command_spec (B S r target fuel entry continuation : ℕ) (G : SimpleGraph (Fin r)) [DecidableRel G.Adj]
    (arrays scalars : List String) (front : List ℕ)
    (ha : "recursion.frames"∉arrays)
    (hv : ∀ s∈scalars,s∉["stack.i","stack.copy.length","stack.words"])
    (hB : front.length+S*arrays.length+scalars.length+r*r+r+target+fuel+entry+continuation+10<B) :
    Spec B (fun σ => NativeStateBounds.Bounded B σ ∧ Prefix front "recursion.frames" σ ∧
      σ.vars "stack.words"=front.length ∧ σ.vars "recursion.stride"=S ∧
      (∀ a∈arrays,(σ.arrs a).length=S) ∧
      front.length+S*arrays.length+scalars.length≤(σ.arrs "recursion.frames").length ∧
      Prefix (NativeWeightReduction.adjacency G) "child.graph" σ ∧ σ.vars "restrict.count"=r ∧
      r*r≤(σ.arrs "search.graph").length ∧ σ.vars "component.target"=target ∧ σ.vars "recursion.fuel"=fuel+1)
      (command arrays scalars entry continuation)
      (fun σ τ => Prefix (front++NativeRecursionFrame.words arrays scalars (σ.setVar "machine.phase" continuation))
          "recursion.frames" τ ∧ τ.vars "stack.words"=front.length+S*arrays.length+scalars.length ∧
        Prefix (NativeWeightReduction.adjacency G) "search.graph" τ ∧ τ.vars "graph.n"=r ∧
        τ.vars "node.k"=target ∧ τ.vars "recursion.fuel"=fuel ∧ τ.vars "machine.phase"=entry)
      ((16*S+8)*arrays.length+7*scalars.length+16*(r*r)+26) := by
  rintro σ ⟨hb,hfront,hwords,hstride,hext,hroom,hgraph,hr,hgraphroom,ht,hfuel⟩
  let ν := σ.setVar "machine.phase" continuation
  have r0 : Run B (.assign "machine.phase" (.lit continuation)) σ ν 2 :=
    Run.assign (evalB_lit (show continuation<B by omega))
  obtain ⟨μ,r1,p1⟩ := NativeRecursionFrame.save_spec B S arrays scalars front ha hv (by omega) ν
    ⟨NativeStateBounds.run r0 hb,hfront,(r0.frame_var _ (by simp [Com.wvars])).trans hwords,
      (r0.frame_var _ (by simp [Com.wvars])).trans hstride,hext,hroom⟩
  have hgraph1 : Prefix (NativeWeightReduction.adjacency G) "child.graph" μ := by
    simpa only [Prefix,r1.frame_arr "child.graph" (save_array arrays scalars _ (by decide)),ν,arrs_setVar] using hgraph
  have hr1 : μ.vars "restrict.count"=r :=
    (r1.frame_var _ (save_variable arrays scalars _ (by decide))).trans
      ((r0.frame_var _ (by simp [Com.wvars])).trans hr)
  obtain ⟨ρ,r2,p2⟩ := NativeChildActivate.command_spec B r G (by omega) μ
    ⟨hgraph1,hr1,by rw [RamFrames.run_array_length (r0.seq r1)]; exact hgraphroom⟩
  have ht2 : ρ.vars "component.target"=target := (r2.frame_var _ (by decide)).trans
    ((r1.frame_var _ (save_variable arrays scalars _ (by decide))).trans
      ((r0.frame_var _ (by simp [Com.wvars])).trans ht))
  have hf2 : ρ.vars "recursion.fuel"=fuel+1 := (r2.frame_var _ (by decide)).trans
    ((r1.frame_var _ (save_variable arrays scalars _ (by decide))).trans
      ((r0.frame_var _ (by simp [Com.wvars])).trans hfuel))
  obtain ⟨τ,r3,p3⟩ := enter_spec B target fuel entry (by omega) ρ ⟨ht2,hf2⟩
  refine ⟨τ,(r0.seq (r1.seq (r2.seq r3))).mono (by omega),?_,?_,?_,?_,p3⟩
  · simpa only [Prefix,(r2.seq r3).frame_arr "recursion.frames"
      (by simp [Com.warrs,enter,NativeChildActivate.command,NativeChildActivate.setup,
        NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append])] using p1.2.1
  · exact ((r2.seq r3).frame_var "stack.words" (by
      simp [Com.wvars,enter,NativeChildActivate.command,NativeChildActivate.setup,
        NativeSlice.command,NativeSlice.read,NativeTabulate.command,NativeTabulate.append,RamWordBuffer.append])).trans p1.2.2
  · simpa only [Prefix,r3.frame_arr "search.graph" (by simp [enter,Com.warrs])] using p2.1
  · exact (r3.frame_var "graph.n" (by simp [enter,Com.wvars])).trans p2.2

end Lax263307Proofs.NativeChildCall
