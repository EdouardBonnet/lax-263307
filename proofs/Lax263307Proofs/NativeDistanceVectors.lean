import Lax263307Proofs.NativeDistanceData
import Lax263307Proofs.NativeDistanceBound

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational Lax455465Proofs.RamVirtualState
open Lax455465Proofs Lax455465Proofs.RamFractionPrimitives
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeDistanceData

def readBound : Com := .seq (.assign "projection.i" (.var "projection.entry")) NativeDistanceBound.command

theorem read_bound_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (i : Fin (rows m n)) (hB : shapeSize m n < B) (hb : Bounded B P x) :
    Spec B (fun σ => Data P x σ ∧ σ.vars "projection.entry"=i.val) readBound
      (fun _ τ => Data P x τ ∧ FractionOutput ((distanceProgram P x).b i) τ) 52 := by
  rintro σ ⟨hd,hi⟩
  have hshape : 3*(m*n)+5*m+5*n+wordLength m n+30 < B := hB
  have hiB : i.val < B := by have hh := i.isLt; dsimp [rows] at hh; omega
  let ν := σ.setVar "projection.i" i.val
  have r1 : Run B (.assign "projection.i" (.var "projection.entry")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hi.symm,hi ▸ hiB⟩)
  have d1 := frame P x r1 hd
    (by simp only [fields,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [arrays,List.mem_cons,forall_eq_or_imp]; decide)
  obtain ⟨τ,r2,p2⟩ := NativeDistanceBound.command_spec B m n P x i (by omega)
    (fun u => (hb.bound u).1) (fun u => (hb.bound u).2) (fun u => (hb.center u).1) (fun u => (hb.center u).2) ν
    ⟨d1.source,d1.center,by simp [ν],d1.oldRows,d1.oldColumns⟩
  have rr := r1.seq r2
  refine ⟨τ,rr,frame P x rr hd
    (by simp only [fields,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [arrays,List.mem_cons,forall_eq_or_imp]; decide),?_⟩
  simpa only [←NativeDistanceEntries.bound_entry P x i] using p2

def readObjective : Com := .ite (.lt (.var "projection.entry") (.var "projection.n")) zero negativeOne

theorem objective_plain_spec (B n j : ℕ) (hB : n+j+3 < B) :
    Spec B (fun σ => σ.vars "projection.entry"=j ∧ σ.vars "projection.n"=n) readObjective
      (fun _ τ => FractionOutput (NativeDistanceEntries.objectiveEntry n j) τ) 10 := by
  have hz := zero_spec B (by omega)
  have hn := negativeOne_spec B (by omega)
  by_cases h : j < n
  · have he : NativeDistanceEntries.objectiveEntry n j=0 := by simp [NativeDistanceEntries.objectiveEntry,h]
    run_vcg [hz,hn]
    all_goals simp_all
  · have he : NativeDistanceEntries.objectiveEntry n j = -1 := by simp [NativeDistanceEntries.objectiveEntry,h]
    run_vcg [hz,hn]
    all_goals simp_all
    all_goals omega

theorem read_objective_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (j : Fin (columns n)) (hB : shapeSize m n < B) :
    Spec B (fun σ => Data P x σ ∧ σ.vars "projection.entry"=j.val) readObjective
      (fun _ τ => Data P x τ ∧ FractionOutput ((distanceProgram P x).c j) τ) 10 := by
  rintro σ ⟨hd,hj⟩
  have hshape : 3*(m*n)+5*m+5*n+wordLength m n+30 < B := hB
  obtain ⟨τ,rr,p⟩ := objective_plain_spec B n j.val (by have hh := j.isLt; dsimp [columns] at hh; omega) σ ⟨hj,hd.oldColumns⟩
  refine ⟨τ,rr,frame P x rr hd
    (by simp only [fields,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [arrays,List.mem_cons,forall_eq_or_imp]; decide),?_⟩
  simpa only [←NativeDistanceEntries.objective_entry P x j] using p

def bounds : Com := RamVectorEncoding.command "projection.entry" "lp.rows" readBound

def objectives : Com := RamVectorEncoding.command "projection.entry" "lp.columns" readObjective

theorem bounds_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (front : List ℕ)
    (hB : shapeSize m n < B) (hb : Bounded B P x) (hlen : front.length+3*rows m n+3 < B) :
    Spec B (fun σ => Data P x σ ∧ Prefix front "lp.word" σ ∧ σ.vars "lp.position"=front.length ∧
      front.length+3*rows m n < (σ.arrs "lp.word").length) bounds
      (fun _ τ => Data P x τ ∧ Prefix (front++encodeVector (distanceProgram P x).b) "lp.word" τ ∧
        τ.vars "lp.position"=front.length+3*rows m n) (87*rows m n+6) := by
  have hh := RamVectorEncoding.command_spec B 52 (Data P x) "projection.entry" "lp.rows"
    (List.ofFn (distanceProgram P x).b) front readBound hb.one (by simpa only [List.length_ofFn] using hlen)
    (by intro i hi; simpa only [List.getElem_ofFn] using (bound_height B P x hb ⟨i,by simpa using hi⟩).1)
    (by intro i hi; simpa only [List.getElem_ofFn] using (bound_height B P x hb ⟨i,by simpa using hi⟩).2)
    (fun σ h => by simpa only [List.length_ofFn] using h.rowCount)
    (fun σ k h => set_entry P x σ k h)
    (by intro i hi; simpa only [List.getElem_ofFn] using read_bound_spec B m n P x ⟨i,by simpa using hi⟩ hB hb)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame P x rr h
      (by simp only [fields,List.mem_cons,forall_eq_or_imp]; decide)
      (by simp only [arrays,List.mem_cons,forall_eq_or_imp]; decide)) (by decide)
  simpa only [bounds,List.length_ofFn,RamVectorEncoding.encode,encodeVector,Nat.reduceAdd] using hh

theorem objectives_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (front : List ℕ)
    (hB : shapeSize m n < B) (hb : Bounded B P x) (hlen : front.length+3*columns n+3 < B) :
    Spec B (fun σ => Data P x σ ∧ Prefix front "lp.word" σ ∧ σ.vars "lp.position"=front.length ∧
      front.length+3*columns n < (σ.arrs "lp.word").length) objectives
      (fun _ τ => Data P x τ ∧ Prefix (front++encodeVector (distanceProgram P x).c) "lp.word" τ ∧
        τ.vars "lp.position"=front.length+3*columns n) (45*columns n+6) := by
  have hh := RamVectorEncoding.command_spec B 10 (Data P x) "projection.entry" "lp.columns"
    (List.ofFn (distanceProgram P x).c) front readObjective hb.one (by simpa only [List.length_ofFn] using hlen)
    (by intro i hi; simpa only [List.getElem_ofFn] using (objective_height B P x hb ⟨i,by simpa using hi⟩).1)
    (by intro i hi; simpa only [List.getElem_ofFn] using (objective_height B P x hb ⟨i,by simpa using hi⟩).2)
    (fun σ h => by simpa only [List.length_ofFn] using h.columnCount)
    (fun σ k h => set_entry P x σ k h)
    (by intro i hi; simpa only [List.getElem_ofFn] using read_objective_spec B m n P x ⟨i,by simpa using hi⟩ hB)
    (by decide) (by decide) (by decide) (by decide)
    (fun rr h => frame P x rr h
      (by simp only [fields,List.mem_cons,forall_eq_or_imp]; decide)
      (by simp only [arrays,List.mem_cons,forall_eq_or_imp]; decide)) (by decide)
  simpa only [objectives,List.length_ofFn,RamVectorEncoding.encode,encodeVector,Nat.reduceAdd] using hh

end Lax263307Proofs.NativeDistanceVectors
