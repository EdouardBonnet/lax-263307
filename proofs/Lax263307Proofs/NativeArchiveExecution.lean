import Lax263307Proofs.NativeWeightedExecution
import Lax263307Proofs.StructuralFrontend
import Lax263307Proofs.MaxWeightIndependentSet

namespace Lax263307Proofs.NativeArchiveExecution

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax455465Proofs
open Lax263307 GraphClasses WeightedIndependentSet
open NativeQptasImplementation

def command {C : GraphClass} (i : Fixed C) : Com :=
  .seq StructuralFrontend.command (BufferedCommand.command (NativeWeightedExecution.command i))

def layout {C : GraphClass} (i : Fixed C) : Layout := RamAutomaticLayout.layout (command i)

def program {C : GraphClass} (i : Fixed C) : Lax213208.Programs.Program :=
  compileProgram (layout i) (command i)

def width {C : GraphClass} (i : Fixed C) {n : ℕ} (w : Fin n → ℚ) (k N : ℕ) : ℕ :=
  NativeQptasWordBounds.width i w (1/((k:ℚ)+1))+N+k+10

def cost {C : GraphClass} (i : Fixed C) {n : ℕ} (w : Fin n → ℚ) (k length : ℕ) : ℕ :=
  14*length+33+8*NativeWeightedExecution.cost i w (1/((k:ℚ)+1))

theorem accuracy_pos (k : ℕ) : (0:ℚ)<1/((k:ℚ)+1) := by positivity

theorem accuracy_lt {k : ℕ} (hk : 0<k) : (1:ℚ)/((k:ℚ)+1)<1 := by
  have hp : (0:ℚ)<k := Nat.cast_pos.mpr hk
  rw [div_lt_one (by positivity)]
  linarith

theorem command_spec {C : GraphClass} (i : Fixed C) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G∈C n) (w : Fin n → ℚ) (k : ℕ) (hk : 0<k) :
    let x := Lax263307.MaxWeightIndependentSet.encodeInstance G w
    ∃ (I : Finset (Fin n)) (ext : String → ℕ),
      IsApproximation G w (1/((k:ℚ)+1)) I ∧
      Spec (2^width i w k (StructuralPacket.size x))
        (fun σ => σ=initEnv ext (StructuralPacket.tape k x)) (command i)
        (fun _ τ => τ.out=encodeOutput I) (cost i w k x.length) := by
  classical
  dsimp only
  let x := Lax263307.MaxWeightIndependentSet.encodeInstance G w
  let ε : ℚ := 1/((k:ℚ)+1)
  let W := width i w k (StructuralPacket.size x)
  have hlen := StructuralPacket.length_le_size x
  have hbits := StructuralPacket.bits_le_size x
  have hW : StructuralPacket.size x+k+10 ≤ W := by dsimp [W,width]; omega
  have hfront : 6*x.length+10 < 2^W :=
    (by omega : 6*x.length+10 ≤ W).trans_lt Nat.lt_two_pow_self
  have hkW : k+1<2^W := (by omega : k+1≤W).trans_lt Nat.lt_two_pow_self
  have hxwords : ∀ v∈x,v<2^W := by
    intro v hv
    exact (WordSize.member_bound x v hv).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hinp : encodeInput G w ε = x++[0,1,k+1] := by
    rw [MaxWeightIndependentSet.input_eq, StructuralPacket.accuracy_encoding]
  obtain ⟨I,ext,happrox,hs⟩ := NativeWeightedExecution.command_spec i G hG w ε
    (accuracy_pos k) (accuracy_lt hk)
  refine ⟨I,StructuralFrontend.extent ext x.length,happrox,?_⟩
  rintro σ rfl
  obtain ⟨μ,r1,hrel⟩ := StructuralFrontend.initial_spec (2^W) k x ext hfront hkW hxwords _ rfl
  obtain ⟨ν,r2,hout⟩ := hs (initEnv ext (encodeInput G w ε)) rfl
  rw [hinp] at r2
  obtain ⟨τ,r3,hrel'⟩ := BufferedCommand.run (B' := 2^W) r2
    (Nat.pow_le_pow_right (by decide) (by dsimp [W,width,ε]; omega))
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by
      intro v hv
      rw [←hinp] at hv
      exact (NativeQptasWordBounds.input i G w ε v hv).trans_le
        (Nat.pow_le_pow_right (by decide) (by dsimp [W,width,ε]; omega))) hrel
  exact ⟨τ,r1.seq r3,hrel'.out.trans hout⟩

/-- Compile the already established high-level specification directly with
lax-62, obtaining the exact execution interface required by lax-213208. -/
theorem result {C : GraphClass} (i : Fixed C) {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G∈C n) (w : Fin n → ℚ) (k : ℕ) (hk : 0<k) :
    let x := Lax263307.MaxWeightIndependentSet.encodeInstance G w
    ∃ I : Finset (Fin n),
      Lax213208.Approximation.IsApproximation Lax263307.MaxWeightIndependentSet
        (1+1/(k:ℝ)) x (encodeOutput I) ∧
      ∀ T : ℕ, width i w k (StructuralPacket.size x)+RamTransfer.layoutAllowance (layout i)≤T →
        10*cost i w k x.length+1≤T →
        Lax213208.Programs.RunsWithin (program i) (StructuralPacket.tape k x) (encodeOutput I) T := by
  dsimp only
  let x := Lax263307.MaxWeightIndependentSet.encodeInstance G w
  let W := width i w k (StructuralPacket.size x)
  obtain ⟨I,ext,happrox,hspec⟩ := command_spec i G hG w k hk
  refine ⟨I,MaxWeightIndependentSet.approximation hk happrox,?_⟩
  intro T hwidth htime
  change W+RamTransfer.layoutAllowance (layout i)≤T at hwidth
  have hW : 0<W := by dsimp [W,width]; omega
  have hsize : StructuralPacket.size x+k+10≤W := by dsimp [W,width]; omega
  refine ⟨StructuralPacket.tape_fits k x T (by omega),?_⟩
  intro wordLength hw
  have hc := Lax62Proofs.Refine.Codegen.computesInTime_of_spec
    (L := layout i) (c := command i) (D := {StructuralPacket.tape k x})
    (f := fun _ => encodeOutput I) (B := fun _ => 2^W)
    (K := fun _ => cost i w k x.length) (w := wordLength)
    (RamAutomaticLayout.layout_ok (command i))
    (by
      rintro input rfl v hv
      exact StructuralPacket.tape_fits k x W hsize v (List.mem_cons_of_mem _ hv))
    (by rintro input rfl; exact ⟨ext,hspec⟩)
    (by intro input hinput; exact RamTransfer.layout_fits hW (hwidth.trans hw))
  intro input hinput
  obtain ⟨steps,hsteps,hrun⟩ := hc input hinput
  exact ⟨steps,(by simpa only [Layout.const] using hsteps : steps≤10*cost i w k x.length+1).trans htime,hrun⟩

end Lax263307Proofs.NativeArchiveExecution
