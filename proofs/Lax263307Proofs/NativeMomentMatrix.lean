import Lax263307Proofs.NativeMomentFamily

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentMatrix

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP NativeMomentFamily

def entryCount (ks : List Kind) (n r : ℕ) : ℕ :=
  (ks.map fun kind => NativeMomentFamily.rowCount kind n r*dimension n r).sum

def words (ks : List Kind) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) : List ℕ :=
  ks.flatMap fun kind => NativeMomentAssembly.matrixWords (matrix kind G k r)

def command (ks : List Kind) : Com := ks.foldr (fun kind c => .seq (NativeMomentFamily.command kind) c) .skip

theorem words_length (ks : List Kind) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    (words ks G k r).length=3*entryCount ks n r := by
  induction ks with
  | nil => simp [words,entryCount]
  | cons kind ks ih =>
    simpa only [words,List.flatMap_cons,List.length_append,NativeMomentAssembly.matrix_length,
      entryCount,List.map_cons,List.sum_cons,Nat.mul_add,Nat.mul_assoc] using congrArg (fun t => 3*NativeMomentFamily.rowCount kind n r*dimension n r+t) ih

theorem command_spec (ks : List Kind) {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (front : List ℕ)
    (hB : front.length+3*entryCount ks n r+n+k+r+dimension n r+10 < B) (hm : 2^n < B) :
    Spec B (fun σ => Data G k r σ ∧ σ.vars "lp.length"=front.length ∧
      front.length+3*entryCount ks n r ≤ (σ.arrs "lp.input").length ∧ Prefix front "lp.input" σ)
      (command ks) (fun _ τ => Data G k r τ ∧ τ.vars "lp.length"=front.length+3*entryCount ks n r ∧
        Prefix (front++words ks G k r) "lp.input" τ)
      ((22*n+129)*entryCount ks n r+12*ks.length+1) := by
  induction ks generalizing front with
  | nil =>
    intro σ hσ
    exact ⟨σ,Run.skip.mono (by simp [entryCount]),hσ.1,by simpa [entryCount] using hσ.2.1,by simpa [words] using hσ.2.2.2⟩
  | cons kind ks ih =>
    have he : entryCount (kind::ks) n r=NativeMomentFamily.rowCount kind n r*dimension n r+entryCount ks n r := rfl
    rintro σ ⟨hd,hl,hr,hp⟩
    obtain ⟨ν,r1,p1⟩ := NativeMomentFamily.command_spec kind B G k r front (by rw [he] at hB; omega) hm σ
      ⟨hd,hl,by rw [he] at hr; omega,hp⟩
    let next := front++NativeMomentAssembly.matrixWords (matrix kind G k r)
    have hlen : next.length=front.length+3*(NativeMomentFamily.rowCount kind n r*dimension n r) := by
      simp only [next,List.length_append,NativeMomentAssembly.matrix_length,Nat.mul_assoc]
    obtain ⟨τ,r2,p2⟩ := ih next (by rw [hlen]; rw [he] at hB; omega) ν
      ⟨p1.1,by rw [hlen]; exact p1.2.1,by rw [hlen,Lax455465Proofs.RamFrames.run_array_length r1]; rw [he] at hr; omega,p1.2.2⟩
    refine ⟨τ,(r1.seq r2).mono (by rw [he,List.length_cons]; nlinarith),p2.1,?_,?_⟩
    · rw [he,hlen] at *
      omega
    · simpa only [next,words,List.flatMap_cons,List.append_assoc] using p2.2.2

def allKinds : List Kind := [.normalization,.upper,.nonindependent,.monotone,.massPositive,.massNegative]

theorem all_count (n r : ℕ) : entryCount allKinds n r=NativeMomentAssembly.rowCount n r*dimension n r := by
  simp only [entryCount,allKinds,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,NativeMomentFamily.rowCount,NativeMomentAssembly.rowCount]
  ring

theorem all_words {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    words allKinds G k r=NativeMomentAssembly.matrixWords (MomentLP.program G k r).A := by
  rw [NativeMomentAssembly.matrix_words_exact]
  simp only [words,allKinds,matrix,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rfl

end Lax263307Proofs.NativeMomentMatrix
