import Lax263307Proofs.BufferedCommand
import Lax263307Proofs.StructuralPacket
import Lax455465Proofs.RamInputCopy
import Lax455465Proofs.RamFrames

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.StructuralFrontend

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs StructuralPacket

def step : Com := .seq (.read "t") (.seq (.read "v") (.seq (.read "t")
  (.seq (.store "" (.var "") (.var "v"))
    (.assign "" (.add (.var "") (.lit 1))))))

def Invariant (xs rest : List ℕ) (σ : Env) : Prop :=
  σ.vars "l" = xs.length ∧ σ.vars "" ≤ xs.length ∧
  σ.inp = triples (xs.drop (σ.vars "")) ++ rest ∧
  (σ.arrs "").length = xs.length+3 ∧
  ∀ j, j < σ.vars "" → (σ.arrs "")[j]? = xs[j]?

theorem step_spec (B : ℕ) (xs rest : List ℕ) (hB : xs.length+6 < B)
    (hwords : ∀ x ∈ xs, x < B) :
    Spec B (fun σ => Invariant xs rest σ ∧ σ.vars "" < xs.length) step
      (fun σ τ => Invariant xs rest τ ∧ τ.vars "" = σ.vars ""+1) 10 := by
  rintro σ ⟨⟨hcount, hindex, hinp, hlength, harrays⟩, hi⟩
  have hhead := RamInputCopy.drop_head xs (σ.vars "") hi
  have hv := hwords xs[σ.vars ""] (List.getElem_mem hi)
  rw [hhead] at hinp
  simp only [triples, List.flatMap_cons, List.cons_append, List.nil_append] at hinp
  have hnext : ∀ j, j < σ.vars ""+1 →
      ((σ.arrs "").set (σ.vars "") xs[σ.vars ""])[j]? = xs[j]? := by
    intro j hj
    by_cases he : σ.vars ""=j
    · subst j
      rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hi]
    · rw [List.getElem?_set_ne he]
      exact harrays j (by omega)
  clear hhead harrays
  run_vcg
  all_goals simp_all [Invariant, triples]

def header : Com := .seq (.read "r") (.seq (.read "t") (.seq (.read "k")
  (.seq (.read "t") (.assign "l" (.div (.sub (.var "r") (.lit 6)) (.lit 6))))))

theorem header_spec (B k : ℕ) (xs rest : List ℕ) (hB : 6*xs.length+6 < B) :
    Spec B (fun σ => σ.inp=(6*xs.length+6)::0::k::0::(triples xs++rest)) header
      (fun _ τ => τ.vars "l"=xs.length ∧ τ.vars "k"=k ∧ τ.inp=triples xs++rest) 10 := by
  intro σ hinp
  have hc : (6*xs.length+6-6)/6 = xs.length := by omega
  run_vcg
  all_goals simp_all <;> omega

def copy : Com := .seq (.assign "" (.lit 0))
  (.while (.lt (.var "") (.var "l")) step)

theorem copy_spec (B : ℕ) (xs rest : List ℕ) (hB : xs.length+6 < B)
    (hwords : ∀ x ∈ xs, x < B) :
    Spec B (fun σ => σ.vars "l"=xs.length ∧ σ.inp=triples xs++rest ∧
      (σ.arrs "").length=xs.length+3) copy
      (fun _ τ => τ.vars "l"=xs.length ∧ τ.inp=rest ∧
        (τ.arrs "").length=xs.length+3 ∧ ∀ j, j<xs.length → (τ.arrs "")[j]?=xs[j]?)
      (14*xs.length+6) := by
  have hlo := Spec.forRangeZero "" "l" (Invariant xs rest) xs.length 10 (by omega)
    (fun _ h => h.2.1) (fun _ h => h.1) (step_spec B xs rest hB hwords)
  rintro σ ⟨hl, hinp, hlen⟩
  obtain ⟨τ, rr, hh⟩ := hlo σ (by
    refine ⟨?_, by simp, ?_, hlen, ?_⟩
    · simpa using hl
    · simpa [triples] using hinp
    · simp)
  refine ⟨τ, rr, hh.1.1, ?_, hh.1.2.2.2.1, ?_⟩
  · simpa [hh.2, triples] using hh.1.2.2.1
  · simpa [hh.2] using hh.1.2.2.2.2

def finish : Com := .seq (.store "" (.var "l") (.lit 0))
  (.seq (.store "" (.add (.var "l") (.lit 1)) (.lit 1))
  (.seq (.store "" (.add (.var "l") (.lit 2)) (.add (.var "k") (.lit 1)))
    (.assign "" (.lit 0))))

theorem finish_array (xs buffer : List ℕ) (k : ℕ) (hlen : buffer.length=xs.length+3)
    (hprefix : ∀ j, j<xs.length → buffer[j]?=xs[j]?) :
    ((buffer.set xs.length 0).set (xs.length+1) 1).set (xs.length+2) (k+1) = xs++[0,1,k+1] := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j<xs.length
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), hprefix j hj, List.getElem?_append_left hj]
  · by_cases h0 : j=xs.length
    · subst j
      simp [List.getElem?_set_ne, List.getElem?_set_self, hlen]
    · by_cases h1 : j=xs.length+1
      · subst j
        simp [List.getElem?_set_ne, List.getElem?_set_self, hlen]
      · by_cases h2 : j=xs.length+2
        · subst j
          simp [List.getElem?_set_self, hlen]
        · rw [List.getElem?_eq_none (by simp [hlen]; omega),
            List.getElem?_eq_none (by simp; omega)]

theorem finish_spec (B k : ℕ) (xs : List ℕ) (hB : xs.length+6 < B) (hk : k+1 < B) :
    Spec B (fun σ => σ.vars "l"=xs.length ∧ σ.vars "k"=k ∧
      (σ.arrs "").length=xs.length+3 ∧ ∀ j, j<xs.length → (σ.arrs "")[j]?=xs[j]?) finish
      (fun _ τ => τ.vars ""=0 ∧ τ.arrs ""=xs++[0,1,k+1]) 17 := by
  rintro σ ⟨hl,hkσ,hlen,hprefix⟩
  have harr := finish_array xs (σ.arrs "") k hlen hprefix
  run_vcg
  all_goals simp_all

def command : Com := .seq header (.seq copy finish)

theorem command_spec (B k : ℕ) (xs : List ℕ) (hB : 6*xs.length+10 < B)
    (hk : k+1 < B) (hwords : ∀ x ∈ xs, x < B) :
    Spec B (fun σ => σ.inp=tape k xs ∧ (σ.arrs "").length=xs.length+3) command
      (fun _ τ => τ.vars ""=0 ∧ τ.arrs ""=xs++[0,1,k+1]) (14*xs.length+33) := by
  rintro σ ⟨hinp, hlen⟩
  obtain ⟨rest, htape⟩ := tape_prefix k xs
  obtain ⟨μ,r1,h1⟩ := header_spec B k xs rest (by omega) σ (hinp.trans htape)
  obtain ⟨ν,r2,h2⟩ := copy_spec B xs rest (by omega) hwords μ
    ⟨h1.1,h1.2.2,by rw [r1.frame_arr "" (by decide)]; exact hlen⟩
  obtain ⟨τ,r3,h3⟩ := finish_spec B k xs (by omega) hk ν
    ⟨h2.1,(r2.frame_var "k" (by decide)).trans h1.2.1,h2.2.2⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by omega),h3⟩

theorem name_frame (x : String) : BufferedCommand.name x ∉ command.wvars := by
  simp [command, header, copy, step, finish, Com.wvars, BufferedCommand.name]
  repeat' constructor
  all_goals intro h; have := congrArg String.toList h; simp at this

theorem name_arr_frame (x : String) : BufferedCommand.name x ∉ command.warrs := by
  simp [command, header, copy, step, finish, Com.warrs]

noncomputable def extent (ext : String → ℕ) (length : ℕ) (a : String) : ℕ :=
  if a="" then length+3 else Function.extend BufferedCommand.name ext (fun _ => 0) a

@[simp] theorem extent_name (ext : String → ℕ) (length : ℕ) (a : String) :
    extent ext length (BufferedCommand.name a) = ext a := by
  simp only [extent, BufferedCommand.name_ne_empty, if_false]
  exact Function.Injective.extend_apply (fun _ _ h => (BufferedCommand.name_eq _ _).mp h) ext _ a

/-- The physical reader establishes exactly the virtual initial state required
by the already proved algorithm, with no solution or advice in the input. -/
theorem initial_spec (B k : ℕ) (xs : List ℕ) (ext : String → ℕ)
    (hB : 6*xs.length+10 < B) (hk : k+1 < B) (hwords : ∀ x ∈ xs, x < B) :
    Spec B (fun σ => σ=initEnv (extent ext xs.length) (tape k xs)) command
      (fun _ τ => BufferedCommand.Rel (xs++[0,1,k+1]) (initEnv ext (xs++[0,1,k+1])) τ)
      (14*xs.length+33) := by
  rintro σ rfl
  obtain ⟨τ,rr,hcursor,hbuffer⟩ := command_spec B k xs hB hk hwords
    (initEnv (extent ext xs.length) (tape k xs)) ⟨rfl,by simp [initEnv,extent]⟩
  refine ⟨τ,rr,?_⟩
  refine ⟨?_,?_,?_,hbuffer,by rw [hcursor]; omega,by simp [initEnv,hcursor]⟩
  · intro x
    rw [rr.frame_var _ (name_frame x)]
    rfl
  · intro a
    rw [rr.frame_arr _ (name_arr_frame a)]
    simp [initEnv]
  · rw [rr.out_eq (by decide)]
    rfl

end Lax263307Proofs.StructuralFrontend
