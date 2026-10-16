import Lax263307Proofs.NativeArchiveExecution
import Lax263307Proofs.NativeQptasComplexity
import Lax263307Proofs.ArchiveRuntime

namespace Lax263307Proofs.ArchiveQptas

open Lax263307 GraphClasses EdgeSublinearSeparators WeightedIndependentSet QPTASRuntime
open Lax455465Proofs
open Lax759944.BinaryWordEncoding (bitSize)
open Lax213208.OptimizationProblem Lax213208.Programs

theorem instance_length {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) :
    (Lax263307.IndependentSetProblem.encodeInstance G w).length = n*n+3*n+1 := by
  classical
  simp [Lax263307.IndependentSetProblem.encodeInstance, encodeRational, List.length_flatten,
    List.length_flatMap, List.sum_ofFn, Finset.sum_const, Nat.mul_comm]

theorem instance_order_bound {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) :
    n ≤ StructuralPacket.size (Lax263307.IndependentSetProblem.encodeInstance G w) := by
  have hh := StructuralPacket.length_le_size (Lax263307.IndependentSetProblem.encodeInstance G w)
  rw [instance_length] at hh
  omega

theorem parameter_bound {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) (k : ℕ) :
    rationalBitSize w (1/((k:ℚ)+1)) ≤
      StructuralPacket.size (Lax263307.IndependentSetProblem.encodeInstance G w)+k+6 := by
  classical
  have hbits := StructuralPacket.bits_le_size (Lax263307.IndependentSetProblem.encodeInstance G w)
  have hpart : bitSize ((List.ofFn w).flatMap encodeRational) ≤
      bitSize (Lax263307.IndependentSetProblem.encodeInstance G w) := by
    simp only [Lax263307.IndependentSetProblem.encodeInstance, WordSize.bitSize_append]
    omega
  have hw := hpart.trans hbits
  have he := StructuralPacket.bits_accuracy k
  rw [rationalBitSize, encodeParameters, WordSize.bitSize_append, StructuralPacket.accuracy_encoding]
  omega

/-- One fixed structured program gives the registered QPTAS on every
canonical graph-and-weight instance. Precision is read at runtime. -/
theorem exists_qptas (C : GraphClass) (hereditary : IsHereditary C)
    (separators : HasStronglyEdgeSublinearSeparators C) :
    ∃ alg, Lax213208.QPTAS.QPTAS (problem := Lax263307.IndependentSetProblem.problem)
      alg (Lax263307.IndependentSetProblem.instances C) := by
  classical
  obtain ⟨i⟩ := NativeQptasImplementation.exists_fixed C hereditary separators
  obtain ⟨K,q,k₀,hq,hk₀,hbounds⟩ := NativeQptasComplexity.exists_bounds i
  let c := K*864^(i.envelopeExponent+1)+q+1
  let d := max (3*(i.envelopeExponent+1)) k₀
  have final (n : ℕ) (weights : Fin n → ℚ) (ε : ℚ) (hε : 0<ε) :
      NativeQptasWordBounds.width i weights ε+NativeQptasRuntime.allowance i+
        10*NativeWeightedExecution.cost i weights ε+1 ≤
      timeBound c d n (rationalBitSize weights ε) ε :=
    (hbounds n weights ε hε).trans (NativeFinalBounds.final_time K (i.envelopeExponent+1) q k₀ n
      (NativeQptasPositive.order weights ε) (rationalBitSize weights ε) ε hε
      (NativeQptasComplexity.copy_bound weights ε hε))
  refine ⟨NativeArchiveExecution.program i,?_⟩
  intro k hk
  let a := RamTransfer.layoutAllowance (NativeArchiveExecution.layout i)
  obtain ⟨q,e,hq,he,htime⟩ := ArchiveRuntime.bound c d k a
  let time := fun N => 2^(q*(Nat.log2 (N+2)+1)^e)
  have hresult : ∀ x ∈ Lax263307.IndependentSetProblem.instances C,
      ∃ y, Lax213208.Approximation.IsApproximation Lax263307.IndependentSetProblem.problem
        (1+1/(k:ℝ)) x y ∧
        RunsWithin (NativeArchiveExecution.program i) (StructuralPacket.tape k x) y
          (time (StructuralPacket.size x)) := by
    rintro x ⟨n,G,w,hG,rfl⟩
    let x := Lax263307.IndependentSetProblem.encodeInstance G w
    let N := StructuralPacket.size x
    let ε : ℚ := 1/((k:ℚ)+1)
    have hh := final n w ε (NativeArchiveExecution.accuracy_pos k)
    have hs := StructuralPacket.length_le_size x
    have ht := htime n (rationalBitSize w ε) N
      (instance_order_bound G w) (parameter_bound G w k)
    obtain ⟨I,happrox,hrun⟩ := NativeArchiveExecution.result i G hG w k hk
    refine ⟨encodeOutput I,happrox,hrun (time N) ?_ ?_⟩
    · apply le_trans (b := 1000*(timeBound c d n (rationalBitSize w ε) ε+N+k+a+100)) ?_ ht
      change NativeQptasWordBounds.width i w ε+N+k+10+a≤_
      omega
    · apply le_trans (b := 1000*(timeBound c d n (rationalBitSize w ε) ε+N+k+a+100)) ?_ ht
      change 10*(14*x.length+33+8*NativeWeightedExecution.cost i w ε)+1≤_
      omega
  constructor
  · refine ⟨le_add_of_nonneg_right (by positivity),?_⟩
    intro x hx
    obtain ⟨y,happrox,hrun⟩ := hresult x hx
    refine ⟨y,?_,happrox⟩
    refine ⟨time (StructuralPacket.size x),?_⟩
    intro wordLength hw
    obtain ⟨steps,hsteps,hr⟩ := hrun.2 wordLength hw (StructuralPacket.tape k x) (Set.mem_singleton _)
    exact ⟨steps,hr⟩
  · refine ⟨q,e,hq,he,?_⟩
    intro x hx
    obtain ⟨y,_,hrun⟩ := hresult x hx
    exact ⟨y,hrun⟩

end Lax263307Proofs.ArchiveQptas
