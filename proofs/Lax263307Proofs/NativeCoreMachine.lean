import Lax263307Proofs.NativeNodeDispatch
import Lax263307Proofs.NativeSmallAttempt
import Lax263307Proofs.NativeLargeNode
import Lax263307Proofs.NativeProjectionPrepare
import Lax263307Proofs.NativeProjectionOracle
import Lax263307Proofs.NativeMomentStorage
import Lax263307Proofs.NativeHeavySearch
import Lax263307Proofs.NativeNearCosts
import Lax263307Proofs.NativeSeparatorOutput
import Lax263307Proofs.NativeComponentDecision
import Lax263307Proofs.NativeComponentLoad
import Lax263307Proofs.NativeComponentControl
import Lax263307Proofs.NativeChildGraph
import Lax263307Proofs.NativeSelectedVertices
import Lax263307Proofs.NativeChildCall
import Lax263307Proofs.NativeStackReturn
import Lax263307Proofs.NativeRoundedControl
import Lax263307Proofs.NativeMachineSegment

namespace Lax263307Proofs.NativeCoreMachine

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Every field is fixed for the graph class, before the input graph,
weights, accuracy, or RAM word width is supplied. -/
structure Config where
  a : ℕ
  K : ℕ
  b : ℕ
  lp : Lax808846.Ram.Program
  flow : Lax808846.Ram.Program
  rounded : Lax808846.Ram.Program
  lpWidth : List ℕ
  flowWidth : List ℕ

def go (phase : ℕ) : Com := .assign "machine.phase" (.lit phase)

def emptyRoot : Com := .seq (.assign "root.mask" (.lit 0))
  (.seq (.assign "root.value" (.lit 0)) (.assign "machine.running" (.lit 0)))

def rootTarget : Com := .ite (.eq (.var "root.target") (.lit 0)) emptyRoot
  (.seq (.assign "node.k" (.var "root.target"))
    (.seq (.assign "recursion.fuel" (.var "root.fuel")) (go 1)))

def rootReply : Com := .ite (.eq (.var "recursion.return.tag") (.lit 1))
  (.seq (.assign "root.mask" (.var "recursion.return.mask"))
    (.seq (.assign "root.value" (.var "root.target")) (.assign "machine.running" (.lit 0))))
  (.seq (.assign "root.target" (.sub (.var "root.target") (.lit 1))) (go 0))

def projectionReply : Com := .ite (.eq (.var "projection.kind") (.lit 0)) (go 6)
  (.ite (.eq (.var "projection.kind") (.lit 1)) (NativeOracleCut.far 13) (NativeAttemptReply.noneCommand 14))

def conditioningReply : Com := .ite (.eq (.var "conditioning.found") (.lit 1))
  (.seq (.assign "conditioning.mask" (.var "conditioning.choice"))
    (.seq NativeNearCosts.command (go 8))) (NativeAttemptReply.noneCommand 14)

def component : Com := .ite (.lt (.var "component.i") (.var "component.count"))
  (.seq NativeComponentLoad.command (go 10))
  (NativeComponentControl.finish 14)

/-- The full finite phase list. Child recursion re-enters phase 1 through
the explicit stack; no recursively expanded command syntax is used. -/
def cases (cfg : Config) (arrays scalars : List String) : List Com :=
  [rootTarget,
   NativeNodeDispatch.command cfg.a cfg.K cfg.b 2 3 14,
   NativeSmallAttempt.command 14,
   .seq (NativeLargeNode.command cfg.a cfg.K cfg.b) (go 4),
   .seq NativeProjectionPrepare.command (.seq (NativeProjectionOracle.command cfg.lp cfg.lpWidth) (go 5)),
   projectionReply,
   .seq NativeMomentStorage.command (.seq NativeHeavySearch.command (go 7)),
   conditioningReply,
   .seq (NativeSeparatorOutput.command cfg.flow cfg.flowWidth) (NativeComponentControl.start 9),
   component,
   .ite (.eq (.var "component.active") (.lit 1)) (go 11) (NativeComponentControl.advance 9),
   .seq NativeChildGraph.command (NativeChildCall.command arrays scalars 1 12),
   NativeComponentControl.childReply 9 13,
   NativeRoundedControl.command cfg.rounded 4 14,
   NativeStackReturn.command arrays scalars 15,
   rootReply]

def frameArrays (cfg : Config) : List String :=
  (((cases cfg [] []).flatMap Com.warrs).dedup).filter (fun a => a != "recursion.frames")

def excludedScalars : List String :=
  ["stack.words","stack.read.i","stack.i","stack.copy.length","recursion.return.tag","recursion.return.mask"]

def frameScalars (cfg : Config) : List String :=
  (((cases cfg [] []).flatMap Com.wvars).dedup).filter (fun s => decide (s∉excludedScalars))

def phases (cfg : Config) : List Com := cases cfg (frameArrays cfg) (frameScalars cfg)

def frameSize (cfg : Config) : Com := .assign "frame.length"
  (.add (.mul (.var "recursion.stride") (.lit (frameArrays cfg).length)) (.lit (frameScalars cfg).length))

def initializeRoot : Com := .seq (.assign "root.target" (.var "graph.n"))
  (.seq (.assign "root.fuel" (.var "recursion.fuel"))
    (.seq (.assign "stack.words" (.lit 0)) (.seq (.assign "machine.running" (.lit 1)) (go 0))))

/-- The unweighted controller, starting after root accuracy and workspace
budgets have been computed. Its complete execution/resource theorem remains
to be established; these definitions do not assert correctness by themselves. -/
def command (cfg : Config) : Com := .seq (frameSize cfg)
  (.seq initializeRoot (NativeMachineTrace.driver (phases cfg)))

theorem phases_length (cfg : Config) : (phases cfg).length=16 := rfl

theorem arrays_nodup (cfg : Config) : (frameArrays cfg).Nodup := by
  apply List.Nodup.filter
  exact List.nodup_dedup _

theorem scalars_nodup (cfg : Config) : (frameScalars cfg).Nodup := by
  apply List.Nodup.filter
  exact List.nodup_dedup _

theorem frames_not_saved (cfg : Config) : "recursion.frames"∉frameArrays cfg := by
  simp [frameArrays]

theorem scalar_not_saved (cfg : Config) (s : String) (hs : s∈excludedScalars) : s∉frameScalars cfg := by
  simp [frameScalars,hs]

theorem scalar_saved (cfg : Config) (s : String) (c : Com)
    (hc : c∈cases cfg [] []) (hs : s∈c.wvars) (he : s∉excludedScalars) : s∈frameScalars cfg := by
  simp only [frameScalars,List.mem_filter,List.mem_dedup,decide_eq_true_eq]
  exact ⟨List.mem_flatMap.mpr ⟨c,hc,hs⟩,he⟩

theorem phase_saved (cfg : Config) : "machine.phase"∈frameScalars cfg := by
  exact scalar_saved cfg _ rootTarget (by simp [cases])
    (by simp [rootTarget,emptyRoot,go,Com.wvars]) (by decide)

theorem running_saved (cfg : Config) : "machine.running"∈frameScalars cfg := by
  exact scalar_saved cfg _ rootTarget (by simp [cases])
    (by simp [rootTarget,emptyRoot,go,Com.wvars]) (by decide)

theorem driver_run {B steps total : ℕ} {cfg : Config} {σ τ : Env}
    (trace : NativeMachineSegment.Segment B (phases cfg) steps total σ τ)
    (halt : τ.vars "machine.running"=0) (hB : 18<B) :
    Run B (NativeMachineTrace.driver (phases cfg)) σ τ (total+68*steps+4) := by
  exact NativeMachineSegment.driver_run trace halt hB

end Lax263307Proofs.NativeCoreMachine
