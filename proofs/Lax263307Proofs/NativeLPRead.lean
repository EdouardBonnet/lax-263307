import Lax263307Proofs.NativeRationalRead
import Lax455465Proofs.FlowLpMatrixList

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeLPRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax455465Proofs.FlowLpMatrixList
open Lax109476.LinearProgram Lax109476.RationalEncoding

def matrixPosition : Com := .assign "read.cursor" (.add (.lit 2) (.mul (.lit 3)
  (.add (.mul (.var "projection.i") (.var "projection.n")) (.var "projection.j"))))

def matrix : Com := .seq matrixPosition (NativeRationalRead.command "lp.input")

theorem matrix_position_spec (B m n : ℕ) (i : Fin m) (j : Fin n)
    (hB : 3*(m*n)+m+n+10 < B) :
    Spec B (fun σ => σ.vars "projection.i"=i.val ∧ σ.vars "projection.j"=j.val ∧ σ.vars "projection.n"=n)
      matrixPosition (fun _ τ => τ.vars "read.cursor"=2+3*(i.val*n+j.val)) 10 := by
  have hi := i.isLt
  have hj := j.isLt
  have hij : i.val*n+j.val < m*n := by
    have hh := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr hi)
    nlinarith
  have hmul : i.val*n ≤ i.val*n+j.val := by omega
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem matrix_spec (B m n : ℕ) (P : Program ℚ m n) (i : Fin m) (j : Fin n)
    (hB : 3*(m*n)+m+n+10 < B) (hn : (P.A i j).num.natAbs < B) (hd : (P.A i j).den < B) :
    Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧ σ.vars "projection.i"=i.val ∧
      σ.vars "projection.j"=j.val ∧ σ.vars "projection.n"=n) matrix
      (fun _ τ => FractionOutput (P.A i j) τ) 27 := by
  rintro σ ⟨hp,hi,hj,hnv⟩
  let z := finProdFinEquiv (i,j)
  have hz : z.val=i.val*n+j.val := by simp [z,finProdFinEquiv]; ring
  have hlen : (values P).length=m*n := List.length_ofFn
  have hzi : z.val < (values P).length := by rw [hlen]; exact z.isLt
  have he : (values P)[z.val]=P.A i j := by
    simp only [values,List.getElem_ofFn,entry]
    change P.A (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1 (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2=P.A i j
    rw [Equiv.symm_apply_apply]
  have hp' : Prefix ([m,n]++(NativeRationalTabulate.words (values P)++(encodeVector P.b++encodeVector P.c))) "lp.input" σ := by
    simpa only [values_eq,NativeRationalTabulate.words,encodeProgram,List.append_assoc] using hp
  obtain ⟨ν,r1,p1⟩ := matrix_position_spec B m n i j hB σ ⟨hi,hj,hnv⟩
  obtain ⟨τ,r2,p2⟩ := NativeRationalRead.vector_entry_spec B "lp.input" [m,n] (encodeVector P.b++encodeVector P.c)
    (values P) z.val hzi (by omega)
    (by simp only [List.length_cons,List.length_nil]; have hh := z.isLt; omega)
    (by rwa [he]) (by rwa [he]) ν
    ⟨by simpa only [Prefix,r1.frame_arr "lp.input" (by decide)] using hp',
      by simpa only [hz,List.length_cons,List.length_nil] using p1⟩
  exact ⟨τ,r1.seq r2,by simpa only [he] using p2.1⟩

def boundPosition : Com := .assign "read.cursor" (.add (.lit 2) (.mul (.lit 3)
  (.add (.mul (.var "projection.m") (.var "projection.n")) (.var "projection.i"))))

def bound : Com := .seq boundPosition (NativeRationalRead.command "lp.input")

theorem bound_position_spec (B m n : ℕ) (i : Fin m) (hB : 3*(m*n)+3*m+n+10 < B) :
    Spec B (fun σ => σ.vars "projection.i"=i.val ∧ σ.vars "projection.m"=m ∧ σ.vars "projection.n"=n)
      boundPosition (fun _ τ => τ.vars "read.cursor"=2+3*(m*n+i.val)) 10 := by
  have hi := i.isLt
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem bound_spec (B m n : ℕ) (P : Program ℚ m n) (i : Fin m)
    (hB : 3*(m*n)+3*m+n+10 < B) (hn : (P.b i).num.natAbs < B) (hd : (P.b i).den < B) :
    Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧ σ.vars "projection.i"=i.val ∧
      σ.vars "projection.m"=m ∧ σ.vars "projection.n"=n) bound
      (fun _ τ => FractionOutput (P.b i) τ) 27 := by
  rintro σ ⟨hp,hi,hmv,hnv⟩
  let front := [m,n]++NativeMomentAssembly.matrixWords P.A
  have hfront : front.length=2+3*(m*n) := by
    simp only [front,List.length_append,List.length_cons,List.length_nil,NativeMomentAssembly.matrix_length,Nat.mul_assoc]
  have hlen : (List.ofFn P.b).length=m := List.length_ofFn
  have hii : i.val < (List.ofFn P.b).length := by rw [hlen]; exact i.isLt
  have he : (List.ofFn P.b)[i.val]=P.b i := by simp
  have hp' : Prefix (front++(NativeRationalTabulate.words (List.ofFn P.b)++encodeVector P.c)) "lp.input" σ := by
    simpa only [front,NativeMomentAssembly.matrixWords,NativeRationalTabulate.words,encodeProgram,encodeVector,List.append_assoc] using hp
  obtain ⟨ν,r1,p1⟩ := bound_position_spec B m n i hB σ ⟨hi,hmv,hnv⟩
  obtain ⟨τ,r2,p2⟩ := NativeRationalRead.vector_entry_spec B "lp.input" front (encodeVector P.c)
    (List.ofFn P.b) i.val hii (by omega)
    (by rw [hfront]; have hh := i.isLt; omega) (by rwa [he]) (by rwa [he]) ν
    ⟨by simpa only [Prefix,r1.frame_arr "lp.input" (by decide)] using hp',by rw [hfront]; omega⟩
  exact ⟨τ,r1.seq r2,by simpa only [he] using p2.1⟩

def centerPosition : Com := .assign "read.cursor" (.mul (.lit 3) (.var "projection.local"))
def center : Com := .seq centerPosition (NativeRationalRead.command "projection.center")

theorem center_spec (B n : ℕ) (x : Fin n → ℚ) (i : Fin n) (hB : 3*n+10 < B)
    (hn : (x i).num.natAbs < B) (hd : (x i).den < B) :
    Spec B (fun σ => Prefix (encodeVector x) "projection.center" σ ∧ σ.vars "projection.local"=i.val) center
      (fun _ τ => FractionOutput (x i) τ) 21 := by
  rintro σ ⟨hp,hi⟩
  let ν := σ.setVar "read.cursor" (3*i.val)
  have hib : i.val < B := i.isLt.trans (by omega)
  have hmul : 3*i.val < B := by have hh := i.isLt; omega
  have r1 : Run B centerPosition σ ν 4 := Run.assign (evalB_bin (op := .mul)
    (evalB_lit (show 3 < B by omega)) (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hib⟩) hmul)
  have hii : i.val < (List.ofFn x).length := by simp
  have he : (List.ofFn x)[i.val]=x i := by simp
  obtain ⟨τ,r2,p2⟩ := NativeRationalRead.vector_entry_spec B "projection.center" [] []
    (List.ofFn x) i.val hii (by omega) (by simp only [List.length_nil]; have hh := i.isLt; omega)
    (by rwa [he]) (by rwa [he]) ν
    ⟨by simpa only [Prefix,r1.frame_arr "projection.center" (by decide),List.nil_append,List.append_nil,NativeRationalTabulate.words,encodeVector] using hp,
      by simp [ν]⟩
  exact ⟨τ,r1.seq r2,by simpa only [he] using p2.1⟩

end Lax263307Proofs.NativeLPRead
