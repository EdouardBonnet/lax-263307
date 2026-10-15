import Lax263307Proofs.NativeMasks
import Lax263307.TargetSearch

namespace Lax263307Proofs.NativeTargetDriver

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 NativeMasks

def privateVars : List String := ["target.i","target.k","target.done","target.mask","target.value"]

def Reply {n : ℕ} (answer : Option (Finset (Fin n))) (σ : Env) : Prop :=
  match answer with
  | none => σ.vars "recursion.return.tag"=0
  | some I => σ.vars "recursion.return.tag"=1 ∧ σ.vars "recursion.return.mask"=mask I

def Outcome {n : ℕ} (attempt : ℕ → Option (Finset (Fin n))) (i : ℕ) (σ : Env) : Prop :=
  (σ.vars "target.done"=0 ∧ σ.vars "target.mask"=0 ∧ σ.vars "target.value"=0 ∧
    TargetSearch.search attempt n=TargetSearch.search attempt (n-i)) ∨
  ∃ I t,σ.vars "target.done"=1 ∧ σ.vars "target.mask"=mask I ∧ σ.vars "target.value"=t ∧
    TargetSearch.search attempt n=(I,t)

def saveResult : Com := .seq (.assign "target.mask" (.var "recursion.return.mask"))
  (.seq (.assign "target.value" (.var "target.k")) (.assign "target.done" (.lit 1)))

def choose : Com := .ite (.eq (.var "recursion.return.tag") (.lit 1)) saveResult .skip
def active (body : Com) : Com := .seq (.assign "target.k" (.sub (.var "graph.n") (.var "target.i")))
  (.seq body choose)
def step (body : Com) : Com := .seq (.ite (.eq (.var "target.done") (.lit 0)) (active body) .skip)
  (.assign "target.i" (.add (.var "target.i") (.lit 1)))

def Invariant {n : ℕ} (Q : Env → Prop) (attempt : ℕ → Option (Finset (Fin n))) (σ : Env) : Prop :=
  Q σ ∧ σ.vars "target.i"≤n ∧ Outcome attempt (σ.vars "target.i") σ


def command (body : Com) : Com := .seq (.assign "target.done" (.lit 0))
  (.seq (.assign "target.mask" (.lit 0)) (.seq (.assign "target.value" (.lit 0))
    (.seq (.assign "target.i" (.lit 0)) (.while (.lt (.var "target.i") (.var "graph.n")) (step body)))))


end Lax263307Proofs.NativeTargetDriver
