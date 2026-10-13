import Lax263307Proofs.NativeDistanceData

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceMatrix

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeDistanceData

def coordinates : Com := .seq (.assign "projection.i" (.div (.var "projection.entry") (.var "lp.columns")))
  (.assign "projection.j" (.sub (.var "projection.entry") (.mul (.var "projection.i") (.var "lp.columns"))))

theorem coordinates_spec (B q cols : ℕ) (hB : q+cols+3 < B) :
    Spec B (fun σ => σ.vars "projection.entry"=q ∧ σ.vars "lp.columns"=cols) coordinates
      (fun _ τ => τ.vars "projection.i"=q/cols ∧ τ.vars "projection.j"=q%cols) 10 := by
  have hdiv : q/cols ≤ q := Nat.div_le_self _ _
  have hmul : q/cols*cols ≤ q := Nat.div_mul_le_self _ _
  run_vcg
  all_goals simp_all [Env.setVar,Nat.mod_eq_sub_div_mul]
  all_goals omega

def read : Com := .seq coordinates NativeDistanceCoefficient.command

theorem read_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (z : Fin (rows m n*columns n)) (hB : shapeSize m n < B) (hb : Bounded B P x) :
    Spec B (fun σ => Data P x σ ∧ σ.vars "projection.entry"=z.val) read
      (fun _ τ => Data P x τ ∧ FractionOutput (FlowLpMatrixList.entry (distanceProgram P x) z) τ) 50 := by
  rintro σ ⟨hd,hz⟩
  have hshape : 3*(m*n)+5*m+5*n+(2+3*(rows m n*columns n+rows m n+columns n))+30 < B := hB
  obtain ⟨ν,r1,p1⟩ := coordinates_spec B z.val (columns n) (by have hh := z.isLt; omega) σ ⟨hz,hd.columnCount⟩
  have d1 := frame P x r1 hd
    (by simp only [fields,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [arrays,List.mem_cons,forall_eq_or_imp]; decide)
  let ij := finProdFinEquiv.symm z
  obtain ⟨τ,r2,p2⟩ := NativeDistanceCoefficient.command_spec B m n P ij.1 ij.2 (by omega)
    (fun u v => (hb.matrix u v).1) (fun u v => (hb.matrix u v).2) ν
    ⟨d1.source,p1.1,d1.oldRows,d1.oldColumns,p1.2⟩
  have rr := r1.seq r2
  refine ⟨τ,rr,frame P x rr hd
    (by simp only [fields,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [arrays,List.mem_cons,forall_eq_or_imp]; decide),?_⟩
  simpa only [←NativeDistanceEntries.matrix_entry P x ij.1 ij.2,FlowLpMatrixList.entry] using p2

def command : Com := RamVectorEncoding.command "projection.entry" "projection.matrixLength" read

theorem command_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (front : List ℕ)
    (hB : shapeSize m n < B) (hb : Bounded B P x)
    (hlen : front.length+3*(rows m n*columns n)+3 < B) :
    Spec B (fun σ => Data P x σ ∧ Prefix front "lp.word" σ ∧ σ.vars "lp.position"=front.length ∧
      front.length+3*(rows m n*columns n) < (σ.arrs "lp.word").length) command
      (fun _ τ => Data P x τ ∧ Prefix (front++NativeMomentAssembly.matrixWords (distanceProgram P x).A) "lp.word" τ ∧
        τ.vars "lp.position"=front.length+3*(rows m n*columns n))
      (85*(rows m n*columns n)+6) := by
  let qs := FlowLpMatrixList.values (distanceProgram P x)
  have hlength : qs.length=rows m n*columns n := List.length_ofFn
  have hh := RamVectorEncoding.command_spec B 50 (Data P x) "projection.entry" "projection.matrixLength" qs front read
    hb.one (by rwa [hlength])
    (by intro i hi; simpa only [qs,FlowLpMatrixList.values,List.getElem_ofFn,FlowLpMatrixList.entry] using (matrix_height B P x hb (finProdFinEquiv.symm ⟨i,by rwa [hlength] at hi⟩).1 (finProdFinEquiv.symm ⟨i,by rwa [hlength] at hi⟩).2).1)
    (by intro i hi; simpa only [qs,FlowLpMatrixList.values,List.getElem_ofFn,FlowLpMatrixList.entry] using (matrix_height B P x hb (finProdFinEquiv.symm ⟨i,by rwa [hlength] at hi⟩).1 (finProdFinEquiv.symm ⟨i,by rwa [hlength] at hi⟩).2).2)
    (fun σ h => by rw [hlength]; exact h.matrixLength)
    (fun σ k h => set_entry P x σ k h)
    (by intro i hi; simpa only [qs,FlowLpMatrixList.values,List.getElem_ofFn] using read_spec B m n P x ⟨i,by rwa [hlength] at hi⟩ hB hb)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame P x rr h
      (by simp only [fields,List.mem_cons,forall_eq_or_imp]; decide)
      (by simp only [arrays,List.mem_cons,forall_eq_or_imp]; decide)) (by decide)
  simp only [hlength] at hh
  simpa only [command,qs,RamVectorEncoding.encode,FlowLpMatrixList.values_eq,NativeMomentAssembly.matrixWords,Nat.reduceAdd] using hh

end Lax263307Proofs.NativeDistanceMatrix
