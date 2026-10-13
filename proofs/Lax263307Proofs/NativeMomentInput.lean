import Lax263307Proofs.NativeMomentMatrix
import Lax263307Proofs.NativeMomentVectors

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax263307 MomentLP NativeMomentFamily
open Lax109476.RationalEncoding

abbrev M (n r : ℕ) := NativeMomentAssembly.rowCount n r

theorem row_count_eq (n r : ℕ) : M n r=2+dimension n r*(n+4) := by
  unfold M NativeMomentAssembly.rowCount
  ring

theorem vector_size (n r : ℕ) : NativeMomentVectors.size n r=M n r+dimension n r := by
  rw [row_count_eq]
  unfold NativeMomentVectors.size
  omega

def rowCountExpr : Expr := .add (.lit 2) (.mul (.var "catalog.count") (.add (.var "graph.n") (.lit 4)))

def header : Com := .seq (.assign "moment.rows" rowCountExpr)
  (.seq (.assign "lp.length" (.lit 0))
    (.seq (RamWordBuffer.append "lp.input" "lp.length" (.var "moment.rows"))
      (RamWordBuffer.append "lp.input" "lp.length" (.var "catalog.count"))))

theorem row_count_spec (B n N : ℕ) (hB : 2+N*(n+4)+n+N+10 < B) :
    Spec B (fun σ => σ.vars "graph.n"=n ∧ σ.vars "catalog.count"=N)
      (.assign "moment.rows" rowCountExpr) (fun _ τ => τ.vars "moment.rows"=2+N*(n+4)) 8 := by
  simp only [rowCountExpr]
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem header_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (hB : M n r+n+dimension n r+10 < B) :
    Spec B (fun σ => Data G k r σ ∧ 2 ≤ (σ.arrs "lp.input").length) header
      (fun _ τ => Data G k r τ ∧ τ.vars "lp.length"=2 ∧ Prefix [M n r,dimension n r] "lp.input" τ) 24 := by
  rintro σ ⟨hd,hr⟩
  obtain ⟨ν,r1,p1⟩ := row_count_spec B n (dimension n r) (by rwa [row_count_eq] at hB) σ ⟨hd.1.1.1,hd.1.1.2.1⟩
  have hrows : ν.vars "moment.rows"=M n r := by rwa [row_count_eq]
  let μ := ν.setVar "lp.length" 0
  have r2 : Run B (.assign "lp.length" (.lit 0)) ν μ 2 := Run.assign (evalB_lit (by omega))
  have hm : μ.vars "moment.rows"=M n r := (r2.frame_var "moment.rows" (by decide)).trans hrows
  have hc : μ.vars "catalog.count"=dimension n r := ((r1.seq r2).frame_var "catalog.count" (by decide)).trans hd.1.1.2.1
  obtain ⟨ξ,r3,p3⟩ := RamWordBuffer.append_spec B "lp.input" "lp.length" [] (M n r) (.var "moment.rows")
    (by omega) (by simp; omega) μ
    ⟨by simp [Prefix],by simp [μ],by rw [RamFrames.run_array_length (r1.seq r2)]; simp only [List.length_nil]; omega,
      by rw [evalB_var_iff]; exact ⟨hm.symm,hm ▸ (by omega)⟩⟩
  have hcξ : ξ.vars "catalog.count"=dimension n r := (r3.frame_var "catalog.count" (by decide)).trans hc
  obtain ⟨τ,r4,p4⟩ := RamWordBuffer.append_spec B "lp.input" "lp.length" [M n r] (dimension n r) (.var "catalog.count")
    (by omega) (by simp; omega) ξ
    ⟨by simpa using p3.1,by simpa using p3.2,
      by rw [RamFrames.run_array_length (r1.seq (r2.seq r3))]; simp only [List.length_singleton]; omega,
      by rw [evalB_var_iff]; exact ⟨hcξ.symm,hcξ ▸ (by omega)⟩⟩
  have rr : Run B header σ τ 24 := r1.seq (r2.seq (r3.seq r4))
  exact ⟨τ,rr,data_frame G k r rr
    (by simp only [fixedVars,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [fixedArrays,List.mem_cons,forall_eq_or_imp]; decide) hd,
    by simpa using p4.2,by simpa using p4.1⟩

def length (n r : ℕ) : ℕ := 2+3*(M n r*dimension n r)+3*(M n r+dimension n r)

def cost (n r : ℕ) : ℕ := (22*n+129)*(M n r*dimension n r)+57*(M n r+dimension n r)+111

def command : Com := .seq header (.seq (NativeMomentMatrix.command NativeMomentMatrix.allKinds) NativeMomentVectors.command)

theorem input_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ) :
    (encodeProgram (MomentLP.program G k r)).length=length n r := by
  have hv : (encodeVector (MomentLP.program G k r).b++encodeVector (MomentLP.program G k r).c).length=3*(M n r+dimension n r) := by
    rw [←NativeMomentVectors.words_exact G k r,NativeRationalTabulate.words_length,NativeMomentVectors.entries_length]
    change 3*NativeMomentVectors.size n r=_
    rw [vector_size]
  change ([M n r,dimension n r]++NativeMomentAssembly.matrixWords (MomentLP.program G k r).A++
    encodeVector (MomentLP.program G k r).b++encodeVector (MomentLP.program G k r).c).length=_
  rw [List.append_assoc ( [M n r,dimension n r]++NativeMomentAssembly.matrixWords (MomentLP.program G k r).A)]
  rw [List.length_append,hv,List.length_append,NativeMomentAssembly.matrix_length]
  simp only [List.length_cons,List.length_nil,length]
  simp only [M,NativeMomentAssembly.rowCount]
  ring

theorem command_spec {n : ℕ} (B : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k r : ℕ)
    (hB : length n r+n+k+r+dimension n r+10 < B) (hm : 2^n < B) :
    Spec B (fun σ => Data G k r σ ∧ length n r ≤ (σ.arrs "lp.input").length) command
      (fun _ τ => Data G k r τ ∧ τ.vars "lp.length"=length n r ∧ Prefix (encodeProgram (MomentLP.program G k r)) "lp.input" τ)
      (cost n r) := by
  rintro σ ⟨hd,hr⟩
  obtain ⟨ν,r1,p1⟩ := header_spec B G k r (by dsimp only [length,M] at hB ⊢; omega) σ ⟨hd,by dsimp only [length,M] at hr; omega⟩
  obtain ⟨μ,r2,p2⟩ := NativeMomentMatrix.command_spec NativeMomentMatrix.allKinds B G k r [M n r,dimension n r]
    (by rw [NativeMomentMatrix.all_count]; simp only [List.length_cons,List.length_nil]; dsimp only [length,M] at hB; omega) hm ν
    ⟨p1.1,p1.2.1,by rw [NativeMomentMatrix.all_count,RamFrames.run_array_length r1]; simp only [List.length_cons,List.length_nil]; dsimp only [length,M] at hr; omega,p1.2.2⟩
  let front := [M n r,dimension n r]++NativeMomentAssembly.matrixWords (MomentLP.program G k r).A
  have hfront : front.length=2+3*(M n r*dimension n r) := by
    simp only [front,List.length_append,List.length_cons,List.length_nil,NativeMomentAssembly.matrix_length,Nat.mul_assoc]
    rfl
  have hp : Prefix front "lp.input" μ := by simpa only [NativeMomentMatrix.all_words] using p2.2.2
  have hl : μ.vars "lp.length"=front.length := by
    simpa only [hfront,NativeMomentMatrix.all_count,List.length_cons,List.length_nil] using p2.2.1
  obtain ⟨τ,r3,p3⟩ := NativeMomentVectors.command_spec B G k r front
    (by rw [hfront,vector_size]; exact hB) μ
    ⟨p2.1,hl,by rw [hfront,vector_size,RamFrames.run_array_length (r1.seq r2)]; exact hr,hp⟩
  refine ⟨τ,(r1.seq (r2.seq r3)).mono (by rw [NativeMomentMatrix.all_count,vector_size]; simp only [NativeMomentMatrix.allKinds,List.length_cons,List.length_nil,cost,M]; omega),p3.1,?_,?_⟩
  · simpa only [hfront,vector_size,length] using p3.2.1
  · change Prefix ([M n r,dimension n r]++NativeMomentAssembly.matrixWords (MomentLP.program G k r).A++
      encodeVector (MomentLP.program G k r).b++encodeVector (MomentLP.program G k r).c) "lp.input" τ
    simpa only [front,List.append_assoc] using p3.2.2

end Lax263307Proofs.NativeMomentInput
