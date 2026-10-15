import Lax263307Proofs.NativeDistanceMetadata
import Lax263307Proofs.NativeDistanceMatrix
import Lax263307Proofs.NativeDistanceVectors

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection NativeDistanceData

def construct : Com := .seq NativeDistanceMetadata.header (.seq NativeDistanceMatrix.command
  (.seq NativeDistanceVectors.bounds NativeDistanceVectors.objectives))

def constructCost (m n : ℕ) : ℕ := 85*(rows m n*columns n)+87*rows m n+45*columns n+34

theorem input_length {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) :
    (encodeProgram (distanceProgram P x)).length=wordLength m n := by
  change ([rows m n,columns n]++NativeMomentAssembly.matrixWords (distanceProgram P x).A++
    RamVectorEncoding.encode (List.ofFn (distanceProgram P x).b)++
    RamVectorEncoding.encode (List.ofFn (distanceProgram P x).c)).length=_
  simp only [List.length_append,List.length_cons,List.length_nil,NativeMomentAssembly.matrix_length,
    RamVectorEncoding.length_encode,List.length_ofFn,wordLength,rows,columns]
  ring

theorem construct_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (hB : shapeSize m n < B) (hb : Bounded B P x) :
    Spec B (fun σ => Data P x σ ∧ wordLength m n < (σ.arrs "lp.word").length) construct
      (fun _ τ => Data P x τ ∧ Prefix (encodeProgram (distanceProgram P x)) "lp.word" τ ∧
        τ.vars "lp.position"=wordLength m n) (constructCost m n) := by
  rintro σ ⟨hd,hr⟩
  have hshape : 3*(m*n)+5*m+5*n+(2+3*(rows m n*columns n+rows m n+columns n))+30 < B := hB
  have hlength : wordLength m n=2+3*(rows m n*columns n)+3*rows m n+3*columns n := by unfold wordLength; ring
  obtain ⟨ν,r1,p1⟩ := NativeDistanceMetadata.header_spec B m n P x hB σ
    ⟨hd,by rw [hlength] at hr; omega⟩
  obtain ⟨μ,r2,p2⟩ := NativeDistanceMatrix.command_spec B m n P x [rows m n,columns n] hB hb
    (by simp only [List.length_cons,List.length_nil]; omega) ν
    ⟨p1.1,p1.2.1,p1.2.2,by rw [RamFrames.run_array_length r1]; simp only [List.length_cons,List.length_nil]; rw [hlength] at hr; omega⟩
  let front := [rows m n,columns n]++NativeMomentAssembly.matrixWords (distanceProgram P x).A
  have hfront : front.length=2+3*(rows m n*columns n) := by
    simp only [front,List.length_append,List.length_cons,List.length_nil,NativeMomentAssembly.matrix_length,Nat.mul_assoc]
  obtain ⟨ξ,r3,p3⟩ := NativeDistanceVectors.bounds_spec B m n P x front hB hb
    (by rw [hfront]; omega) μ
    ⟨p2.1,p2.2.1,by rw [hfront]; simpa only [List.length_cons,List.length_nil] using p2.2.2,
      by rw [hfront,RamFrames.run_array_length (r1.seq r2)]; rw [hlength] at hr; omega⟩
  let next := front++encodeVector (distanceProgram P x).b
  have hnext : next.length=2+3*(rows m n*columns n)+3*rows m n := by
    change (front++RamVectorEncoding.encode (List.ofFn (distanceProgram P x).b)).length=_
    rw [List.length_append,RamVectorEncoding.length_encode,List.length_ofFn,hfront]
  obtain ⟨τ,r4,p4⟩ := NativeDistanceVectors.objectives_spec B m n P x next hB hb
    (by rw [hnext]; omega) ξ
    ⟨p3.1,p3.2.1,by rw [hnext]; simpa only [hfront] using p3.2.2,
      by rw [hnext,RamFrames.run_array_length (r1.seq (r2.seq r3))]; rw [hlength] at hr; omega⟩
  refine ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by dsimp [constructCost]; omega),p4.1,?_,?_⟩
  · simpa only [next,front,NativeMomentAssembly.matrixWords,encodeProgram] using p4.2.1
  · simpa only [hnext,hlength] using p4.2.2

def command : Com := .seq NativeDistanceMetadata.command construct

def cost (m n : ℕ) : ℕ := 85*(rows m n*columns n)+87*rows m n+45*columns n+54

/-- Rebuild the exact distance-query LP from the existing canonical base
LP and current rational center. Both source buffers are preserved. -/
theorem command_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ)
    (hB : shapeSize m n < B) (hb : Bounded B P x) :
    Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧ Prefix (encodeVector x) "projection.center" σ ∧
      wordLength m n < (σ.arrs "lp.word").length) command
      (fun _ τ => Data P x τ ∧ Prefix (encodeProgram (distanceProgram P x)) "lp.word" τ ∧
        τ.vars "lp.position"=wordLength m n) (cost m n) := by
  rintro σ ⟨hp,hx,hr⟩
  obtain ⟨ν,r1,p1⟩ := NativeDistanceMetadata.command_spec B m n P x hB σ ⟨hp,hx⟩
  obtain ⟨τ,r2,p2⟩ := construct_spec B m n P x hB hb ν
    ⟨p1,by rwa [RamFrames.run_array_length r1]⟩
  exact ⟨τ,(r1.seq r2).mono (by dsimp [cost,constructCost]; omega),p2⟩


end Lax263307Proofs.NativeDistanceInput
