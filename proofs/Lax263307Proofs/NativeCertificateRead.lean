import Lax263307Proofs.NativeRationalRead
import Lax263307.DistanceProjection
import Lax455465Proofs.RamVectorEncoding

namespace Lax263307Proofs.NativeCertificateRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax263307.DistanceProjection

def tag : Com := .assign "projection.tag" (.get "vm.output" (.lit 0))

def tagValue {m n : ℕ} : Certificate m n → ℕ
  | .optimal _ _ => 0
  | .infeasible _ => 1
  | .unbounded _ _ => 2

theorem tag_spec (B : ℕ) {m n : ℕ} (c : Certificate m n) (h3 : 3<B) :
    Spec B (Prefix (encodeCertificate c) "vm.output") tag
      (fun _ τ => τ.vars "projection.tag"=tagValue c) 3 := by
  intro σ hp
  have hget : (σ.arrs "vm.output")[0]?=some (tagValue c) := by
    cases c <;> simpa [encodeCertificate,tagValue] using hp 0 (by simp [encodeCertificate])
  have hv : tagValue c<B := by cases c <;> dsimp [tagValue] <;> omega
  have hread : (Expr.get "vm.output" (.lit 0)).evalB B σ=some (tagValue c) := by
    exact evalB_get (evalB_lit (show 0<B by omega)) hget hv
  exact ⟨σ.setVar "projection.tag" (tagValue c),Run.assign hread,by simp⟩

def primalPosition : Com := .assign "read.cursor"
  (.add (.lit 1) (.mul (.lit 3) (.var "certificate.index")))
def primal : Com := .seq primalPosition (NativeRationalRead.command "vm.output")

theorem primal_spec (B m n : ℕ) (z : Fin (n+1) → ℚ) (dual : Fin (m+(n+n)) → ℚ)
    (i : Fin (n+1)) (hB : 3*n+10<B) (hn : (z i).num.natAbs<B) (hd : (z i).den<B) :
    Spec B (fun σ => Prefix (encodeCertificate (.optimal z dual)) "vm.output" σ ∧
      σ.vars "certificate.index"=i.val) primal
      (fun _ τ => RamRational.FractionOutput (z i) τ) 23 := by
  rintro σ ⟨hp,hi⟩
  have hpos : Spec B (fun σ => σ.vars "certificate.index"=i.val) primalPosition
      (fun _ τ => τ.vars "read.cursor"=1+3*i.val) 6 := by
    intro μ hh
    run_vcg
    all_goals simp_all
  obtain ⟨ν,r1,p1⟩ := hpos σ hi
  have hpν : Prefix ([0]++RamVectorEncoding.encode (List.ofFn z)++encodeVector dual) "vm.output" ν := by
    simpa only [Prefix,r1.frame_arr "vm.output" (by decide),encodeCertificate,encodeVector,RamVectorEncoding.encode,NativeRationalTabulate.words,List.append_assoc] using hp
  obtain ⟨τ,r2,p2⟩ := NativeRationalRead.vector_entry_spec B "vm.output" [0] (encodeVector dual)
    (List.ofFn z) i.val (by simpa using i.isLt) (by omega) (by simp; omega)
    (by simpa only [List.getElem_ofFn] using hn) (by simpa only [List.getElem_ofFn] using hd) ν
    ⟨by simpa only [RamVectorEncoding.encode,NativeRationalTabulate.words,List.append_assoc] using hpν,by simpa using p1⟩
  exact ⟨τ,(r1.seq r2),by simpa only [List.getElem_ofFn] using p2.1⟩

def dualPosition : Com := .assign "read.cursor" (.add (.lit 1)
  (.mul (.lit 3) (.add (.add (.var "projection.n") (.lit 1)) (.var "certificate.index"))))
def dual : Com := .seq dualPosition (NativeRationalRead.command "vm.output")

theorem dual_spec (B m n : ℕ) (z : Fin (n+1) → ℚ) (y : Fin (m+(n+n)) → ℚ)
    (i : Fin (m+(n+n))) (hB : 3*m+10*n+20<B)
    (hn : (y i).num.natAbs<B) (hd : (y i).den<B) :
    Spec B (fun σ => Prefix (encodeCertificate (.optimal z y)) "vm.output" σ ∧
      σ.vars "projection.n"=n ∧ σ.vars "certificate.index"=i.val) dual
      (fun _ τ => RamRational.FractionOutput (y i) τ) 27 := by
  rintro σ ⟨hp,hN,hi⟩
  have hpos : Spec B (fun σ => σ.vars "projection.n"=n ∧ σ.vars "certificate.index"=i.val) dualPosition
      (fun _ τ => τ.vars "read.cursor"=1+3*(n+1+i.val)) 10 := by
    rintro μ ⟨hhN,hhi⟩
    run_vcg
    all_goals simp_all
  obtain ⟨ν,r1,p1⟩ := hpos σ ⟨hN,hi⟩
  let front := [0]++encodeVector z
  have hfront : front.length=1+3*(n+1) := by
    change ([0]++RamVectorEncoding.encode (List.ofFn z)).length=_
    simp only [List.length_append,List.length_cons,List.length_nil,
      RamVectorEncoding.length_encode,List.length_ofFn]
  have hpν : Prefix (front++RamVectorEncoding.encode (List.ofFn y)++[]) "vm.output" ν := by
    simpa only [front,Prefix,r1.frame_arr "vm.output" (by decide),encodeCertificate,encodeVector,RamVectorEncoding.encode,NativeRationalTabulate.words,List.append_nil,List.append_assoc] using hp
  obtain ⟨τ,r2,p2⟩ := NativeRationalRead.vector_entry_spec B "vm.output" front [] (List.ofFn y)
    i.val (by simpa using i.isLt) (by omega) (by rw [hfront]; omega)
    (by simpa only [List.getElem_ofFn] using hn) (by simpa only [List.getElem_ofFn] using hd) ν
    ⟨by simpa only [RamVectorEncoding.encode,NativeRationalTabulate.words,List.append_assoc] using hpν,by rw [hfront]; omega⟩
  exact ⟨τ,r1.seq r2,by simpa only [List.getElem_ofFn] using p2.1⟩

end Lax263307Proofs.NativeCertificateRead
