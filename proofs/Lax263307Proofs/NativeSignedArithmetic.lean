import Lax455465Proofs.RamComparison

namespace Lax263307Proofs.NativeSignedArithmetic

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamRational

/-- A reduced rational held in three ordinary RAM variables. Either sign
for zero is allowed, matching the registered exact arithmetic routines. -/
def Stored (name : String) (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars (name++".s")) (σ.vars (name++".n")) (σ.vars (name++".d"))=q ∧
    σ.vars (name++".n")=q.num.natAbs ∧ σ.vars (name++".d")=q.den ∧
    σ.vars (name++".s")≤1

def save (name : String) : Com := .seq (.assign (name++".s") (.var "rat.s"))
  (.seq (.assign (name++".n") (.var "rat.n")) (.assign (name++".d") (.var "rat.d")))

def load (name : String) : Com := .seq (.assign "rat.s" (.var (name++".s")))
  (.seq (.assign "rat.n" (.var (name++".n"))) (.assign "rat.d" (.var (name++".d"))))

theorem save_spec (B : ℕ) (name : String) (q : ℚ) (h1 : 1<B)
    (hn : q.num.natAbs<B) (hd : q.den<B)
    (hfresh : name++".s"≠"rat.n" ∧ name++".s"≠"rat.d" ∧ name++".n"≠"rat.d") :
    Spec B (FractionOutput q) (save name) (fun _ τ => Stored name q τ) 6 := by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hsB : σ.vars "rat.s"<B := hs.trans_lt h1
  have hsN := Ne.symm hfresh.1
  have hsD := Ne.symm hfresh.2.1
  have hnD := Ne.symm hfresh.2.2
  run_vcg
  all_goals simp_all [Stored]

theorem load_spec (B : ℕ) (name : String) (q : ℚ) (h1 : 1<B)
    (hn : q.num.natAbs<B) (hd : q.den<B)
    (hfresh : name++".n"≠"rat.s" ∧ name++".d"≠"rat.s" ∧ name++".d"≠"rat.n") :
    Spec B (Stored name q) (load name) (fun _ τ => FractionOutput q τ) 6 := by
  rintro σ ⟨hv,hnσ,hdσ,hs⟩
  have hsB : σ.vars (name++".s")<B := hs.trans_lt h1
  run_vcg
  all_goals simp_all [FractionOutput]

def Operands (a b : ℚ) (σ : Env) : Prop := Stored "left" a σ ∧ Stored "right" b σ

def Bounded (M : ℕ) (q : ℚ) : Prop := q.num.natAbs≤M ∧ q.den≤M

theorem add_spec (B M : ℕ) (a b : ℚ) (hB : 2*M^2+3<B)
    (ha : Bounded M a) (hb : Bounded M b) :
    Spec B (Operands a b) addFraction (fun _ τ => FractionOutput (a+b) τ)
      (36*(a.den*b.den).size+96) := by
  rintro σ ⟨hleft,hright⟩
  simp only [Stored,String.reduceAppend] at hleft hright
  obtain ⟨τ,rr,ht⟩ := addFraction_spec B M (σ.vars "left.s") a.num.natAbs a.den
    (σ.vars "right.s") b.num.natAbs b.den hB hleft.2.2.2 hright.2.2.2
    ha.1 ha.2 hb.1 hb.2 a.den_pos b.den_pos σ
    ⟨rfl,hleft.2.1,hleft.2.2.1,rfl,hright.2.1,hright.2.2.1⟩
  have hl : fractionValue (σ.vars "left.s") a.num.natAbs a.den=a := by
    simpa only [← hleft.2.1,← hleft.2.2.1] using hleft.1
  have hr : fractionValue (σ.vars "right.s") b.num.natAbs b.den=b := by
    simpa only [← hright.2.1,← hright.2.2.1] using hright.1
  exact ⟨τ,rr,by simpa only [hl,hr] using ht⟩

theorem multiply_spec (B M : ℕ) (a b : ℚ) (hB : 2*M^2+3<B)
    (ha : Bounded M a) (hb : Bounded M b) :
    Spec B (Operands a b) multiplyFraction (fun _ τ => FractionOutput (a*b) τ)
      (36*(a.den*b.den).size+64) := by
  rintro σ ⟨hleft,hright⟩
  simp only [Stored,String.reduceAppend] at hleft hright
  obtain ⟨τ,rr,ht⟩ := multiplyFraction_spec B M (σ.vars "left.s") a.num.natAbs a.den
    (σ.vars "right.s") b.num.natAbs b.den hB hleft.2.2.2 hright.2.2.2
    ha.1 ha.2 hb.1 hb.2 a.den_pos b.den_pos σ
    ⟨rfl,hleft.2.1,hleft.2.2.1,rfl,hright.2.1,hright.2.2.1⟩
  have hl : fractionValue (σ.vars "left.s") a.num.natAbs a.den=a := by
    simpa only [← hleft.2.1,← hleft.2.2.1] using hleft.1
  have hr : fractionValue (σ.vars "right.s") b.num.natAbs b.den=b := by
    simpa only [← hright.2.1,← hright.2.2.1] using hright.1
  exact ⟨τ,rr,by simpa only [hl,hr] using ht⟩

theorem compare_spec (B M : ℕ) (a b : ℚ) (hB : 2*M^2+3<B)
    (ha : Bounded M a) (hb : Bounded M b) :
    Spec B (Operands a b) Lax455465Proofs.RamComparison.compareFraction
      (fun _ τ => τ.vars "cmp.le"=if a≤b then 1 else 0) 40 := by
  rintro σ ⟨hleft,hright⟩
  simp only [Stored,String.reduceAppend] at hleft hright
  obtain ⟨τ,rr,ht⟩ := Lax455465Proofs.RamComparison.compareFraction_spec B M
    (σ.vars "left.s") a.num.natAbs a.den (σ.vars "right.s") b.num.natAbs b.den
    hB hleft.2.2.2 hright.2.2.2 ha.1 ha.2 hb.1 hb.2 a.den_pos b.den_pos σ
    ⟨rfl,hleft.2.1,hleft.2.2.1,rfl,hright.2.1,hright.2.2.1⟩
  have hl : fractionValue (σ.vars "left.s") a.num.natAbs a.den=a := by
    simpa only [← hleft.2.1,← hleft.2.2.1] using hleft.1
  have hr : fractionValue (σ.vars "right.s") b.num.natAbs b.den=b := by
    simpa only [← hright.2.1,← hright.2.2.1] using hright.1
  rw [hl,hr] at ht
  refine ⟨τ,rr,?_⟩
  split_ifs with h
  · exact ht.2.mpr h
  · have hne := mt ht.2.mp h
    have hle := ht.1
    omega

end Lax263307Proofs.NativeSignedArithmetic
