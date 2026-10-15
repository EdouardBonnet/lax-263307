import Lax263307Proofs.NativeCoreMachine
import Lax263307Proofs.NativeBlowUp
import Lax263307Proofs.NativeRootAccuracy
import Lax263307Proofs.NativeOriginalAccuracy
import Lax263307Proofs.NativeRootBudget
import Lax263307Proofs.NativeEmptyOutput
import Lax263307Proofs.NativeWeightedOutput
import Lax263307Proofs.NativeQptasTransfer

namespace Lax263307Proofs.NativeQptasProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet

def order : Com := .assign "graph.n" (.var "blowup.length")

def copyGraph : Com := .seq (.assign "matrix.length" (.mul (.var "graph.n") (.var "graph.n")))
  (NativeProgramCache.copy "blowup.matrix" "search.graph" "matrix.length")

/-- The complete finite source program. Configuration and budget constants
are fixed for the graph class; no input graph, weights, accuracy or word width
is a parameter of this program definition. Correctness still requires the
complete recursive command specification and common resource invariant. -/
def command (cfg : NativeCoreMachine.Config) (C d Q e : ℕ) : Com :=
  .seq NativeBlowUp.prepare (.seq order
    (.ite (.eq (.var "graph.n") (.lit 0)) NativeEmptyOutput.command
      (.seq copyGraph (.seq NativeOriginalAccuracy.command (.seq NativeRootAccuracy.command (.seq (NativeRootBudget.command C d Q e)
        (.seq (NativeCoreMachine.command cfg) NativeWeightedOutput.command)))))))

def layout (cfg : NativeCoreMachine.Config) (C d Q e : ℕ) : Layout :=
  RamAutomaticLayout.layout (command cfg C d Q e)

def program (cfg : NativeCoreMachine.Config) (C d Q e : ℕ) : Lax808846.Ram.Program :=
  compileProgram (layout cfg C d Q e) (command cfg C d Q e)

theorem layout_ok (cfg : NativeCoreMachine.Config) (C d Q e : ℕ) :
    Com.Ok (layout cfg C d Q e) (command cfg C d Q e) := RamAutomaticLayout.layout_ok _

/-- Activate the actual prepared blow-up graph as the unweighted controller's
working graph. No graph is supplied as runtime advice. -/
theorem copy_graph_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hB : n*n+n+5<B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ Prefix (NativeWeightReduction.adjacency G) "blowup.matrix" σ ∧
      n*n≤(σ.arrs "search.graph").length) copyGraph
      (fun _ τ => τ.vars "graph.n"=n ∧ Prefix (NativeWeightReduction.adjacency G) "search.graph" τ)
      (16*(n*n)+14) := by
  rintro σ ⟨hn,hgraph,hroom⟩
  let ν := σ.setVar "matrix.length" (n*n)
  have hvar : (Expr.var "graph.n").evalB B σ=some n := by
    rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega)⟩
  have r1 : Run B (.assign "matrix.length" (.mul (.var "graph.n") (.var "graph.n"))) σ ν 4 :=
    Run.assign (evalB_bin (op:=.mul) hvar hvar (by change n*n<B; omega))
  have hlen : (NativeWeightReduction.adjacency G).length=n*n := by
    simp [NativeWeightReduction.adjacency,List.length_flatten,List.sum_ofFn,Finset.sum_const,Nat.mul_comm]
  have hw : ∀ z∈NativeWeightReduction.adjacency G,z<B := by
    intro z hz
    simp only [NativeWeightReduction.adjacency,List.mem_flatten,List.mem_ofFn] at hz
    obtain ⟨row,⟨i,rfl⟩,hz⟩ := hz
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz
    split_ifs <;> omega
  obtain ⟨τ,r2,p2⟩ := NativeProgramCache.copy_spec B "blowup.matrix" "search.graph" "matrix.length"
    (NativeWeightReduction.adjacency G) (by decide) (by rw [hlen]; omega) hw ν
    ⟨by simpa [Prefix,ν] using hgraph,by simp [ν,hlen],by simpa [ν,hlen] using hroom⟩
  exact ⟨τ,(r1.seq r2).mono (by rw [hlen]; omega),
    (r2.frame_var _ (by decide)).trans ((r1.frame_var _ (by decide)).trans hn),p2.2⟩

/-- A zero-size blow-up makes the functional weighted answer empty as well,
including the branch where the original graph itself is nonempty. -/
theorem zero_size_result {n : ℕ} (lp flow : List ℕ → List ℕ) (a K b : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (weights : Fin n → ℚ) (ε : ℚ)
    (hzero : (∑ v,WeightRounding.copies (PositiveWeights.positiveWeights weights) ε v)=0) :
    WeightedAlgorithm.solve lp flow a K b G weights ε=∅ := by
  let cs := WeightRounding.copies (PositiveWeights.positiveWeights weights) ε
  let I := RecursiveAlgorithm.independentSet lp flow a K b (WeightedAlgorithm.numbered G cs) (ε/2)
  have hI : I=∅ := by
    ext v
    have hv := v.isLt
    change v.val<∑ w,cs w at hv
    change (∑ w,cs w)=0 at hzero
    omega
  dsimp only [WeightedAlgorithm.solve]
  split_ifs
  · rfl
  · change PositiveWeights.discardNonpositive weights
      (IndependentBlowUp.project (I.image (WeightedAlgorithm.labeling cs)))=∅
    simp [hI,IndependentBlowUp.project,PositiveWeights.discardNonpositive]

end Lax263307Proofs.NativeQptasProgram
