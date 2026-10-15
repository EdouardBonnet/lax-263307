import Lax263307.NativeMomentLP
import Lax263307Proofs.NativeMomentSetup
import Lax263307Proofs.NativeArrayBounds

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax263307 MomentLP
open Lax109476.RationalEncoding

abbrev N (n r : ℕ) := dimension n r
abbrev L (n r : ℕ) := NativeMomentInput.length n r

abbrev encodeInput := @Lax263307.NativeMomentLP.encodeInput

def readInput : Com := .seq (.read "graph.n") (.seq (.read "row.k") (.seq (.read "moment.r")
  (.seq RamInputCopy.copy (RamArrayCopy.command "input.data" "search.graph" "input.length"))))

theorem read_input_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (hB : n*n+n+k+r+3 < B) :
    Spec B (fun σ => σ.inp=encodeInput G k r ∧ n*n ≤ (σ.arrs "input.data").length ∧ n*n ≤ (σ.arrs "search.graph").length)
      readInput (fun _ τ => τ.vars "graph.n"=n ∧ τ.vars "row.k"=k ∧ τ.vars "moment.r"=r ∧
        Prefix (NativeWeightReduction.adjacency G) "search.graph" τ) (24*n*n+16) := by
  let xs := NativeWeightReduction.adjacency G
  have hl : xs.length=n*n := NativeWeightReduction.adjacency_length G
  have hw : ∀ z ∈ xs,z < B := fun z hz => (NativeExhaustive.adjacency_words G z hz).trans_lt (by omega)
  rintro σ ⟨hinp,hroom,hgraph⟩
  let ν := {σ.setVar "graph.n" n with inp := k::r::(n*n)::xs}
  have r1 : Run B (.read "graph.n") σ ν 1 := Run.read hinp
  let μ := {ν.setVar "row.k" k with inp := r::(n*n)::xs}
  have r2 : Run B (.read "row.k") ν μ 1 := Run.read rfl
  let ξ := {μ.setVar "moment.r" r with inp := (n*n)::xs}
  have r3 : Run B (.read "moment.r") μ ξ 1 := Run.read rfl
  have r123 := r1.seq (r2.seq r3)
  obtain ⟨ρ,r4,p4⟩ := RamInputCopy.copy_spec B xs (by omega) (by omega) hw ξ
    ⟨by simp [ξ,hl],by rw [RamFrames.run_array_length r123,hl]; exact hroom⟩
  obtain ⟨τ,r5,p5⟩ := RamArrayCopy.command_spec B xs "input.data" "search.graph" "input.length"
    (by omega) (by omega) hw (by decide) (by decide) ρ
    ⟨p4.2.2,p4.1,by rw [RamFrames.run_array_length (r123.seq r4),hl]; exact hgraph⟩
  have rr := r4.seq r5
  refine ⟨τ,(r1.seq (r2.seq (r3.seq rr))).mono (by rw [hl]; nlinarith),?_,?_,?_,p5.2⟩
  · rw [rr.frame_var "graph.n" (by decide)]; simp [ξ,μ,ν]
  · rw [rr.frame_var "row.k" (by decide)]; simp [ξ,μ]
  · rw [rr.frame_var "moment.r" (by decide)]; simp [ξ]

def emit : Com := .seq (.assign "emit.count" (.var "lp.length")) (RamEmitWords.command "lp.input" 1)

theorem emit_spec (B : ℕ) (xs : List ℕ) (hB : xs.length+2 < B) (hw : ∀ z ∈ xs,z < B) :
    Spec B (fun σ => σ.vars "lp.length"=xs.length ∧ Prefix xs "lp.input" σ) emit
      (fun σ τ => τ.out=σ.out++xs) (13*xs.length+8) := by
  rintro σ ⟨hl,hp⟩
  let ν := σ.setVar "emit.count" xs.length
  have r1 : Run B (.assign "emit.count" (.var "lp.length")) σ ν 2 := Run.assign
    (by rw [evalB_var_iff]; exact ⟨hl.symm,hl ▸ (by omega)⟩)
  obtain ⟨τ,r2,p2⟩ := RamEmitWords.command_spec B "lp.input" 1 xs σ.out (by omega) (by omega)
    (by simpa only [one_mul] using (show xs.length < B by omega)) (by omega) hw ν
    ⟨by simpa only [RamEmitWords.Data,Prefix,one_mul,ν,arrs_setVar] using hp,by simp [ν],rfl⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),p2⟩

def fullCommand : Com := .seq readInput (.seq NativeMomentSetup.command (.seq NativeMomentInput.command emit))

def totalCost (n r : ℕ) : ℕ := 24*n*n+16+NativeMomentSetup.cost n r+NativeMomentInput.cost n r+13*L n r+8

theorem full_command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (hB : NativeMomentSetup.guardBound n k r < B) (hm : 2^n < B) :
    Spec B (fun σ => σ.inp=encodeInput G k r ∧ NativeArrayBounds.Bounded B σ ∧
      ∀ a,NativeMomentSetup.guardBound n k r ≤ (σ.arrs a).length)
      fullCommand (fun σ τ => τ.out=σ.out++encodeProgram (MomentLP.program G k r)) (totalCost n r) := by
  rintro σ ⟨hinp,hbounded,hroom⟩
  have hg : n*n+(n+1)*(r+3)+L n r+n+k+r+N n r+20 < B := hB
  obtain ⟨ν,r1,p1⟩ := read_input_spec B G k r (by omega) σ
    ⟨hinp,by have hh := hroom "input.data"; dsimp [NativeMomentSetup.guardBound] at hh; omega,
      by have hh := hroom "search.graph"; dsimp [NativeMomentSetup.guardBound] at hh; omega⟩
  have hrν : ∀ a,NativeMomentSetup.guardBound n k r ≤ (ν.arrs a).length := fun a => by rw [RamFrames.run_array_length r1]; exact hroom a
  obtain ⟨μ,r2,p2⟩ := NativeMomentSetup.command_spec B G k r hB hm ν
    ⟨p1.1,p1.2.1,p1.2.2.1,p1.2.2.2,
      by have hh := hrν "choose.table"; dsimp [NativeMomentSetup.guardBound] at hh; omega,
      by have hh := hrν "subset.bits"; dsimp [NativeMomentSetup.guardBound] at hh; omega,
      by have hh := hrν "catalog.mask"; dsimp [NativeMomentSetup.guardBound] at hh; omega,
      by have hh := hrν "catalog.card"; dsimp [NativeMomentSetup.guardBound] at hh; omega,
      by have hh := hrν "catalog.independent"; dsimp [NativeMomentSetup.guardBound] at hh; omega⟩
  obtain ⟨ξ,r3,p3⟩ := NativeMomentInput.command_spec B G k r (by change L n r+n+k+r+N n r+10 < B; omega) hm μ
    ⟨p2,by rw [RamFrames.run_array_length (r1.seq r2)]; have hh := hroom "lp.input"; dsimp [NativeMomentSetup.guardBound] at hh; omega⟩
  have rr := r1.seq (r2.seq r3)
  have hw := NativeArrayBounds.prefix_words (NativeArrayBounds.run rr hbounded) p3.2.2
  obtain ⟨τ,r4,p4⟩ := emit_spec B (encodeProgram (MomentLP.program G k r))
    (by rw [NativeMomentInput.input_length]; change L n r+2 < B; omega) hw ξ
    ⟨by rw [NativeMomentInput.input_length]; exact p3.2.1,p3.2.2⟩
  have hout : ξ.out=σ.out := rr.out_eq (by decide)
  exact ⟨τ,(r1.seq (r2.seq (r3.seq r4))).mono (by rw [NativeMomentInput.input_length]; dsimp only [totalCost,L]; omega),by rwa [hout] at p4⟩

open Lax109476Proofs

def layout := RamAutomaticLayout.layout fullCommand
def program : Lax808846.Ram.Program := Lax808846Proofs.Compile.compileProgram layout fullCommand


def size (n k r : ℕ) : ℕ := n+k+r+N n r+2

theorem polynomial_bounds (n k r : ℕ) :
    NativeMomentSetup.guardBound n k r ≤ 73*(size n k r)^3 ∧ totalCost n r ≤ 2646*(size n k r)^4 := by
  let X := size n k r
  have hN : 1 ≤ N n r := NativeMomentFamily.dimension_positive n r
  have hX : 1 ≤ X := by dsimp [X,size]; omega
  have hn : n ≤ X := by dsimp [X,size]; omega
  have hk : k ≤ X := by dsimp [X,size]; omega
  have hr : r ≤ X := by dsimp [X,size]; omega
  have hNc : N n r ≤ X := by dsimp [X,size]; omega
  have hn1 : n+1 ≤ X := by dsimp [X,size]; omega
  have hr3 : r+3 ≤ X := by dsimp [X,size]; omega
  have h12 : X ≤ X^2 := le_self_pow hX (by omega)
  have h23 : X^2 ≤ X^3 := Nat.pow_le_pow_right hX (by omega)
  have h34 : X^3 ≤ X^4 := Nat.pow_le_pow_right hX (by omega)
  have h02 : 1 ≤ X^2 := Nat.one_le_pow _ _ (by omega)
  have h03 : 1 ≤ X^3 := Nat.one_le_pow _ _ (by omega)
  have h04 : 1 ≤ X^4 := Nat.one_le_pow _ _ (by omega)
  have hn2 : n*n ≤ X^2 := by simpa only [pow_two] using Nat.mul_le_mul hn hn
  have hdim : (n+1)*(r+3) ≤ X^2 := by simpa only [pow_two] using Nat.mul_le_mul hn1 hr3
  have hM : NativeMomentInput.M n r ≤ 7*X^2 := by
    rw [NativeMomentInput.row_count_eq]
    have hh := Nat.mul_le_mul hNc (show n+4 ≤ 5*X by omega)
    nlinarith only [hh,h02]
  have hMN : NativeMomentInput.M n r*N n r ≤ 7*X^3 := by
    have hh := Nat.mul_le_mul hM hNc
    nlinarith only [hh]
  have hL : L n r ≤ 47*X^3 := by
    change 2+3*(NativeMomentInput.M n r*N n r)+3*(NativeMomentInput.M n r+N n r) ≤ _
    nlinarith only [hMN,hM,hNc,h12,h23,h03]
  have hguard : NativeMomentSetup.guardBound n k r ≤ 73*X^3 := by
    change n*n+(n+1)*(r+3)+L n r+n+k+r+N n r+20 ≤ _
    nlinarith only [hn2,hdim,hL,hn,hk,hr,hNc,h12,h23,h03]
  have hcat : NativeMomentSetup.catalogCost n r ≤ 205*X^3 := by
    have hh := Nat.mul_le_mul (show 69*n+33 ≤ 102*X by omega) hNc
    have ht : 54*(n+1)*(r+3)+(69*n+33)*N n r+41 ≤ 197*X^2 := by
      nlinarith only [hh,hdim,h02]
    have hp := Nat.mul_le_mul ht hr3
    change (54*(n+1)*(r+3)+(69*n+33)*N n r+41)*(r+3)+8 ≤ _
    nlinarith only [hp,h03]
  have hsetup : NativeMomentSetup.cost n r ≤ 363*X^3 := by
    have hc : 38*n*n+42*n+60 ≤ 140*X^2 := by nlinarith only [hn2,hn,h12,h02]
    have hh := Nat.mul_le_mul hc hNc
    change NativeMomentSetup.catalogCost n r+(38*n*n+42*n+60)*N n r+18 ≤ _
    nlinarith only [hh,hcat,h03]
  have hinput : NativeMomentInput.cost n r ≤ 1624*X^4 := by
    have hc : 22*n+129 ≤ 151*X := by omega
    have hh := Nat.mul_le_mul hc hMN
    change (22*n+129)*(NativeMomentInput.M n r*N n r)+57*(NativeMomentInput.M n r+N n r)+111 ≤ _
    nlinarith only [hh,hM,hNc,h12,h23,h34,h04]
  refine ⟨hguard,?_⟩
  change 24*n*n+16+NativeMomentSetup.cost n r+NativeMomentInput.cost n r+13*L n r+8 ≤ _
  nlinarith only [hn2,hsetup,hinput,hL,h23,h34,h04]


end Lax263307Proofs.NativeMomentProgram
