import Lax263307Proofs.NativeDistanceData

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeDistanceMetadata

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.LinearProgram Lax109476.RationalEncoding
open NativeDistanceData

def readDimensions : Com := .seq (.assign "projection.m" (.get "lp.input" (.lit 0)))
  (.assign "projection.n" (.get "lp.input" (.lit 1)))

theorem read_dimensions_spec (B m n : ℕ) (P : Program ℚ m n) (hB : m+n+3 < B) :
    Spec B (Prefix (encodeProgram P) "lp.input") readDimensions
      (fun _ τ => τ.vars "projection.m"=m ∧ τ.vars "projection.n"=n) 6 := by
  intro σ hp
  have hm : (σ.arrs "lp.input")[0]?=some m := by
    have hh := hp 0 (by simp [encodeProgram])
    simpa [encodeProgram] using hh
  have hn : (σ.arrs "lp.input")[1]?=some n := by
    have hh := hp 1 (by simp [encodeProgram])
    simpa [encodeProgram] using hh
  let ν := σ.setVar "projection.m" m
  have r1 : Run B (.assign "projection.m" (.get "lp.input" (.lit 0))) σ ν 3 :=
    Run.assign (evalB_get (evalB_lit (show 0 < B by omega)) hm (by omega))
  let τ := ν.setVar "projection.n" n
  have r2 : Run B (.assign "projection.n" (.get "lp.input" (.lit 1))) ν τ 3 :=
    Run.assign (evalB_get (evalB_lit (show 1 < B by omega)) hn (by omega))
  exact ⟨τ,r1.seq r2,by simp [τ,ν],by simp [τ]⟩

def sizes : Com := .seq (.assign "lp.rows" (.add (.var "projection.m") (.add (.var "projection.n") (.var "projection.n"))))
  (.seq (.assign "lp.columns" (.add (.var "projection.n") (.lit 1)))
    (.assign "projection.matrixLength" (.mul (.var "lp.rows") (.var "lp.columns"))))

theorem sizes_spec (B m n : ℕ) (hB : shapeSize m n < B) :
    Spec B (fun σ => σ.vars "projection.m"=m ∧ σ.vars "projection.n"=n) sizes
      (fun _ τ => τ.vars "lp.rows"=rows m n ∧ τ.vars "lp.columns"=columns n ∧
        τ.vars "projection.matrixLength"=rows m n*columns n) 14 := by
  have hshape : 3*(m*n)+5*m+5*n+(2+3*(rows m n*columns n+rows m n+columns n))+30 < B := hB
  have hprod : (m+(n+n))*(n+1) < B := by change rows m n*columns n < B; omega
  run_vcg
  all_goals simp_all [rows,columns,Env.setVar]

def command : Com := .seq readDimensions sizes

theorem command_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (hB : shapeSize m n < B) :
    Spec B (fun σ => Prefix (encodeProgram P) "lp.input" σ ∧ Prefix (encodeVector x) "projection.center" σ)
      command (fun _ τ => Data P x τ) 20 := by
  rintro σ ⟨hp,hx⟩
  have hshape : 3*(m*n)+5*m+5*n+wordLength m n+30 < B := hB
  obtain ⟨ν,r1,p1⟩ := read_dimensions_spec B m n P (by omega) σ hp
  obtain ⟨τ,r2,p2⟩ := sizes_spec B m n hB ν p1
  have rr := r1.seq r2
  refine ⟨τ,rr,?_⟩
  constructor
  · simpa only [Prefix,rr.frame_arr "lp.input" (by decide)] using hp
  · simpa only [Prefix,rr.frame_arr "projection.center" (by decide)] using hx
  · exact (r2.frame_var "projection.m" (by decide)).trans p1.1
  · exact (r2.frame_var "projection.n" (by decide)).trans p1.2
  · exact p2.1
  · exact p2.2.1
  · exact p2.2.2

def header : Com := .seq (.assign "lp.position" (.lit 0))
  (.seq (RamWordBuffer.append "lp.word" "lp.position" (.var "lp.rows"))
    (RamWordBuffer.append "lp.word" "lp.position" (.var "lp.columns")))

theorem header_spec (B m n : ℕ) (P : Program ℚ m n) (x : Fin n → ℚ) (hB : shapeSize m n < B) :
    Spec B (fun σ => Data P x σ ∧ 2 < (σ.arrs "lp.word").length) header
      (fun _ τ => Data P x τ ∧ Prefix [rows m n,columns n] "lp.word" τ ∧ τ.vars "lp.position"=2) 16 := by
  rintro σ ⟨hd,hr⟩
  have hshape : 3*(m*n)+5*m+5*n+(2+3*(rows m n*columns n+rows m n+columns n))+30 < B := hB
  have hrowB : rows m n < B := by omega
  have hcolB : columns n < B := by omega
  let ν := σ.setVar "lp.position" 0
  have r1 : Run B (.assign "lp.position" (.lit 0)) σ ν 2 := Run.assign (evalB_lit (by omega))
  have hrow : ν.vars "lp.rows"=rows m n := hd.rowCount
  obtain ⟨μ,r2,p2⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position" [] (rows m n) (.var "lp.rows")
    (by omega) (by simp; omega) ν
    ⟨by simp [Prefix],by simp [ν],by simp only [List.length_nil]; exact Nat.lt_trans (by omega) hr,
      by rw [evalB_var_iff]; exact ⟨hrow.symm,hrow ▸ hrowB⟩⟩
  have hcol : μ.vars "lp.columns"=columns n := ((r1.seq r2).frame_var "lp.columns" (by decide)).trans hd.columnCount
  obtain ⟨τ,r3,p3⟩ := RamWordBuffer.append_spec B "lp.word" "lp.position" [rows m n] (columns n) (.var "lp.columns")
    (by omega) (by simp; omega) μ
    ⟨by simpa using p2.1,by simpa using p2.2,
      by rw [RamFrames.run_array_length (r1.seq r2)]; simp only [List.length_singleton]; omega,
      by rw [evalB_var_iff]; exact ⟨hcol.symm,hcol ▸ hcolB⟩⟩
  have rr := r1.seq (r2.seq r3)
  exact ⟨τ,rr,frame P x rr hd
    (by simp only [fields,List.mem_cons,forall_eq_or_imp]; decide)
    (by simp only [arrays,List.mem_cons,forall_eq_or_imp]; decide),by simpa using p3.1,by simpa using p3.2⟩

end Lax263307Proofs.NativeDistanceMetadata
