import Lax455465Proofs.RamBitSize
import Lax263307Proofs.AlgorithmParameters

namespace Lax263307Proofs.NativeLogarithms

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307.AlgorithmParameters
open Lax455465Proofs

theorem size_eq (n : ℕ) (hn : 0<n) : n.size=Nat.log2 n+1 := by
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self (by decide) n
  · have hp : 2^Nat.log2 n≤n := by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 (by omega)
    have hs := Nat.lt_size.mpr hp
    omega

def small : Com := .seq (.assign "size.value" (.var "graph.n"))
  (.seq RamBitSize.word (.assign "node.log" (.var "size.count")))

def large : Com := .seq (.assign "size.value" (.mul (.lit 2) (.var "graph.n")))
  (.seq RamBitSize.word (.assign "node.logarithm" (.var "size.count")))

def command : Com := .seq small large

theorem small_spec (B n : ℕ) (hn : 0<n) (hB : n+3<B) :
    Spec B (fun σ => σ.vars "graph.n"=n) small
      (fun _ τ => τ.vars "graph.n"=n ∧ τ.vars "node.log"=Nat.log2 n+1) (12*n.size+10) := by
  intro σ hs
  let ν := σ.setVar "size.value" n
  have r1 : Run B (.assign "size.value" (.var "graph.n")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hs.symm,by omega⟩)
  obtain ⟨μ,r2,p2⟩ := RamBitSize.word_spec B n (by omega) (by omega) ν (by rfl)
  let τ := μ.setVar "node.log" n.size
  have hsize : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  have r3 : Run B (.assign "node.log" (.var "size.count")) μ τ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨p2.2.symm,by rw [p2.2]; omega⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),((r1.seq (r2.seq r3)).frame_var "graph.n" (by decide)).trans hs,
    by change n.size=Nat.log2 n+1; exact size_eq n hn⟩

theorem large_spec (B n : ℕ) (hn : 0<n) (hB : 2*n+3<B) :
    Spec B (fun σ => σ.vars "graph.n"=n) large
      (fun _ τ => τ.vars "graph.n"=n ∧ τ.vars "node.logarithm"=logarithm n) (12*(2*n).size+12) := by
  intro σ hs
  let ν := σ.setVar "size.value" (2*n)
  have r1 : Run B (.assign "size.value" (.mul (.lit 2) (.var "graph.n"))) σ ν 4 := Run.assign
    (evalB_bin (op:=.mul) (evalB_lit (show 2<B by omega))
      (by rw [evalB_var_iff]; exact ⟨hs.symm,by omega⟩) (by change 2*n<B; omega))
  obtain ⟨μ,r2,p2⟩ := RamBitSize.word_spec B (2*n) (by omega) (by omega) ν (by rfl)
  let τ := μ.setVar "node.logarithm" (2*n).size
  have hsize : (2*n).size≤2*n := Nat.size_le.mpr Nat.lt_two_pow_self
  have r3 : Run B (.assign "node.logarithm" (.var "size.count")) μ τ 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨p2.2.symm,by rw [p2.2]; omega⟩)
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),((r1.seq (r2.seq r3)).frame_var "graph.n" (by decide)).trans hs,
    by change (2*n).size=Nat.log2 (2*n)+1; exact size_eq (2*n) (by omega)⟩

/-- Compute both binary logarithm factors used in node parameters,
with no dependence on the ambient RAM word width. -/
theorem command_spec (B n : ℕ) (hn : 0<n) (hB : 2*n+3<B) :
    Spec B (fun σ => σ.vars "graph.n"=n) command
      (fun _ τ => τ.vars "graph.n"=n ∧ τ.vars "node.log"=Nat.log2 n+1 ∧
        τ.vars "node.logarithm"=logarithm n) (12*n.size+12*(2*n).size+22) := by
  intro σ hs
  obtain ⟨ν,r1,p1⟩ := small_spec B n hn (by omega) σ hs
  obtain ⟨τ,r2,p2⟩ := large_spec B n hn hB ν p1.1
  exact ⟨τ,(r1.seq r2).mono (by omega),p2.1,
    (r2.frame_var "node.log" (by decide)).trans p1.2,p2.2⟩

end Lax263307Proofs.NativeLogarithms
