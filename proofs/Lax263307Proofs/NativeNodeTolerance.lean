import Lax263307Proofs.NativeNodePrecision
import Lax263307Proofs.NativeProgramCache
import Lax455465Proofs.RamFractionEncoding
import Lax263307.ProjectedOracle

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeNodeTolerance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState Lax455465Proofs.RamRational
open Lax109476.RationalEncoding
open Lax263307

def denominator (n D R : ℕ) : ℕ := 32*n*n*D*D*R
def tolerance (n D R : ℕ) : ℚ := 1/(denominator n D R : ℚ)
def guard (n D R : ℕ) : ℕ := 32+n+D+R+32*n+32*n*n+32*n*n*D+32*n*n*D*D+denominator n D R+20
def Context (n D R : ℕ) (σ : Env) : Prop :=
  σ.vars "graph.n"=n ∧ σ.vars "node.D"=D ∧ σ.vars "node.floorPower"=R

theorem coordinates (n D R : ℕ) (hn : 0<n) (hD : 0<D) (hR : 0<R) :
    (tolerance n D R).num=1 ∧ (tolerance n D R).den=denominator n D R := by
  have hp : 0<denominator n D R := by unfold denominator; positivity
  have he : tolerance n D R=mkRat 1 (denominator n D R) := by simp [tolerance,Rat.mkRat_eq_div]
  rw [he]
  simp [Rat.num_mkRat,Rat.den_mkRat,ne_of_gt hp]

def setup : Com := .seq (.assign "rat.s" (.lit 0))
  (.seq (.assign "rat.n" (.lit 1))
    (.seq (.assign "rat.d" (.mul (.mul (.mul (.mul (.mul (.lit 32) (.var "graph.n"))
      (.var "graph.n")) (.var "node.D")) (.var "node.D")) (.var "node.floorPower")))
      (.assign "lp.position" (.lit 0))))

def command : Com := .seq setup (.seq RamFractionEncoding.emit
  (NativeProgramCache.copy "lp.word" "projection.tolerance" "lp.position"))

theorem setup_spec (B n D R : ℕ) (hn : 0<n) (hD : 0<D) (hR : 0<R) (hB : guard n D R<B) :
    Spec B (Context n D R) setup
      (fun _ τ => Context n D R τ ∧ FractionOutput (tolerance n D R) τ ∧ τ.vars "lp.position"=0) 18 := by
  have hcoords := coordinates n D R hn hD hR
  have hv : fractionValue 0 1 (denominator n D R)=tolerance n D R := by simp [fractionValue,tolerance]
  intro σ hs
  run_vcg
  all_goals simp_all [Context,FractionOutput,Env.setVar,guard,denominator,hcoords.1,hcoords.2,hv]
  all_goals omega

theorem context_frame {B n D R t : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ t)
    (hs : Context n D R σ) (hn : "graph.n"∉c.wvars) (hD : "node.D"∉c.wvars)
    (hR : "node.floorPower"∉c.wvars) : Context n D R τ :=
  ⟨(rr.frame_var _ hn).trans hs.1,(rr.frame_var _ hD).trans hs.2.1,(rr.frame_var _ hR).trans hs.2.2⟩

/-- Compute and store the exact rational projection tolerance from
the original graph order, accuracy denominator, and computed moment floor. -/
theorem command_spec (B n D R : ℕ) (hn : 0<n) (hD : 0<D) (hR : 0<R) (hB : guard n D R<B) :
    Spec B (fun σ => Context n D R σ ∧ 3≤(σ.arrs "lp.word").length ∧
      3≤(σ.arrs "projection.tolerance").length) command
      (fun _ τ => Context n D R τ ∧ Prefix (encodeRational (tolerance n D R)) "projection.tolerance" τ) 103 := by
  have hcoords := coordinates n D R hn hD hR
  have hd : denominator n D R<B := by dsimp only [guard] at hB; omega
  have h1 : 1<B := by dsimp only [guard] at hB; omega
  have he : encodeRational (tolerance n D R)=[0,1,denominator n D R] := by
    simp [encodeRational,hcoords.1,hcoords.2]
  have hw : ∀ z∈encodeRational (tolerance n D R),z<B := by
    rw [he]
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> omega
  have hlen : (encodeRational (tolerance n D R)).length=3 := by rw [he]; rfl
  rintro σ ⟨hs,hword,hroom⟩
  obtain ⟨ν,r1,p1⟩ := setup_spec B n D R hn hD hR hB σ hs
  obtain ⟨μ,r2,p2⟩ := RamFractionEncoding.emit_spec B (tolerance n D R) [] h1
    (by simpa only [hcoords.1,Int.natAbs_one] using h1) (by rw [hcoords.2]; exact hd)
    (by dsimp only [guard] at hB; simp; omega) ν
    ⟨p1.2.1,by simp [Prefix],by simpa only [List.length_nil] using p1.2.2,
      by rw [RamFrames.run_array_length r1]; simp; omega⟩
  obtain ⟨τ,r3,p3⟩ := NativeProgramCache.copy_spec B "lp.word" "projection.tolerance" "lp.position"
    (encodeRational (tolerance n D R)) (by decide) (by rw [hlen]; dsimp only [guard] at hB; omega) hw μ
    ⟨by simpa only [List.nil_append] using p2.1,
      by simpa only [hlen,List.length_nil,Nat.zero_add] using p2.2,
      by rw [hlen,RamFrames.run_array_length r2,RamFrames.run_array_length r1]; exact hroom⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [hlen]),
    context_frame (r2.seq r3) p1.1 (by decide) (by decide) (by decide),p3.2⟩

theorem actual_tolerance (a K b n D : ℕ) :
    tolerance n D ((AlgorithmParameters.floorDenominator a K b n D)^(AlgorithmParameters.level a K b n D))=
      Lax263307.ProjectedOracle.tolerance a K b n D := by
  unfold tolerance denominator Lax263307.ProjectedOracle.tolerance AlgorithmParameters.momentFloor
  rw [div_div]
  simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
  congr 1
  ring

end Lax263307Proofs.NativeNodeTolerance
