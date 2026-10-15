import Lax263307Proofs.NativeWeightReduction

namespace Lax263307Proofs.NativeOriginalAccuracy

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 WeightedIndependentSet NativeFrontend

/-- Read the original accuracy from the retained input, after activating
the blow-up graph. The offset uses original input.n, not the blow-up order. -/
def command : Com := .seq (.assign "source.accuracy"
  (.add (.mul (.var "input.n") (.var "input.n")) (.mul (.lit 3) (.var "input.n"))))
  (.seq (.assign "accuracy.n" (.get "input.data" (.add (.var "source.accuracy") (.lit 1))))
    (.assign "accuracy.d" (.get "input.data" (.add (.var "source.accuracy") (.lit 2)))))

theorem command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (weights : Fin n → ℚ) (ε : ℚ) (hB : n*n+3*n+3<B)
    (hn : ε.num.natAbs<B) (hd : ε.den<B) :
    Spec B (fun σ => σ.vars "input.n"=n ∧ Prefix (tailInput G weights ε) "input.data" σ)
      command (fun _ τ => τ.vars "accuracy.n"=ε.num.natAbs ∧ τ.vars "accuracy.d"=ε.den) 18 := by
  rintro σ ⟨horder,hinput⟩
  have hnB : n<B := by nlinarith only [hB]
  have hvar : (Expr.var "input.n").evalB B σ=some n := by
    rw [evalB_var_iff]; exact ⟨horder.symm,horder ▸ hnB⟩
  let offset := n*n+3*n
  let ν := σ.setVar "source.accuracy" offset
  have r1 : Run B (.assign "source.accuracy"
      (.add (.mul (.var "input.n") (.var "input.n")) (.mul (.lit 3) (.var "input.n")))) σ ν 8 :=
    Run.assign (evalB_bin (op:=.add)
      (evalB_bin (op:=.mul) hvar hvar (by change n*n<B; omega))
      (evalB_bin (op:=.mul) (evalB_lit (show 3<B by omega)) hvar (by change 3*n<B; omega))
      (by change offset<B; dsimp [offset]; omega))
  have hnum : (tailInput G weights ε)[offset+1]?=some ε.num.natAbs := by
    have hmatrix : (NativeWeightReduction.adjacency G).length=n*n := NativeWeightReduction.adjacency_length G
    have hw : ((List.ofFn weights).flatMap encodeRational).length=3*n := by
      simp [encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const,Nat.mul_comm]
    change (NativeWeightReduction.adjacency G++((List.ofFn weights).flatMap encodeRational++encodeRational ε))[offset+1]?=_
    rw [List.getElem?_append_right (by dsimp [offset]; omega),hmatrix]
    rw [List.getElem?_append_right (by dsimp [offset]; omega),hw]
    have hi : offset+1-n*n-3*n=1 := by dsimp [offset]; omega
    rw [hi]; rfl
  have hden : (tailInput G weights ε)[offset+2]?=some ε.den := by
    have hmatrix : (NativeWeightReduction.adjacency G).length=n*n := NativeWeightReduction.adjacency_length G
    have hw : ((List.ofFn weights).flatMap encodeRational).length=3*n := by
      simp [encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const,Nat.mul_comm]
    change (NativeWeightReduction.adjacency G++((List.ofFn weights).flatMap encodeRational++encodeRational ε))[offset+2]?=_
    rw [List.getElem?_append_right (by dsimp [offset]; omega),hmatrix]
    rw [List.getElem?_append_right (by dsimp [offset]; omega),hw]
    have hi : offset+2-n*n-3*n=2 := by dsimp [offset]; omega
    rw [hi]; rfl
  have hindex1 : offset+1<(tailInput G weights ε).length := by rw [tail_length]; dsimp [offset]; omega
  have hindex2 : offset+2<(tailInput G weights ε).length := by rw [tail_length]; dsimp [offset]; omega
  have hnumσ := (hinput _ hindex1).trans (by simpa only [List.getElem?_eq_getElem hindex1] using hnum)
  have hdenσ := (hinput _ hindex2).trans (by simpa only [List.getElem?_eq_getElem hindex2] using hden)
  let μ := ν.setVar "accuracy.n" ε.num.natAbs
  have r2 : Run B (.assign "accuracy.n" (.get "input.data" (.add (.var "source.accuracy") (.lit 1)))) ν μ 5 :=
    Run.assign (evalB_get
      (evalB_bin (op:=.add) (by rw [evalB_var_iff]; simp [ν]; dsimp [offset]; omega)
        (evalB_lit (show 1<B by omega)) (by change offset+1<B; dsimp [offset]; omega)) hnumσ hn)
  let τ := μ.setVar "accuracy.d" ε.den
  have r3 : Run B (.assign "accuracy.d" (.get "input.data" (.add (.var "source.accuracy") (.lit 2)))) μ τ 5 :=
    Run.assign (evalB_get
      (evalB_bin (op:=.add) (by rw [evalB_var_iff]; simp [μ,ν]; dsimp [offset]; omega)
        (evalB_lit (show 2<B by omega)) (by change offset+2<B; dsimp [offset]; omega)) hdenσ hd)
  exact ⟨τ,r1.seq (r2.seq r3),by simp [τ,μ],by simp [τ]⟩

end Lax263307Proofs.NativeOriginalAccuracy
