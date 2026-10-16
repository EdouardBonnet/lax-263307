import Lax62Proofs.Refine.Codegen.Cash
import Mathlib.Tactic

/-! A structured command can consume a prepared array instead of the physical
input tape. Names are isolated by a fixed injective prefix. The simulation is
entirely at the structured-command level; the registered compiler handles the
subsequent descent to the word RAM. -/

namespace Lax263307Proofs.BufferedCommand

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def name (x : String) : String := "!" ++ x

@[simp] theorem name_eq (x y : String) : name x = name y ↔ x = y := by
  simp [name]

@[simp] theorem name_ne_empty (x : String) : name x ≠ "" := by
  simp [name, String.append_eq_empty_iff]

@[simp] theorem empty_ne_name (x : String) : "" ≠ name x := (name_ne_empty x).symm

def expr : Expr → Expr
  | .lit n => .lit n
  | .var x => .var (name x)
  | .get a i => .get (name a) (expr i)
  | .bin op e f => .bin op (expr e) (expr f)

def cond : Cond → Cond
  | .eq e f => .eq (expr e) (expr f)
  | .lt e f => .lt (expr e) (expr f)

def read (x : String) : Com := .seq
  (.assign (name x) (.get "" (.var "")))
  (.assign "" (.add (.var "") (.lit 1)))

def command : Com → Com
  | .skip => .skip
  | .assign x e => .assign (name x) (expr e)
  | .store a i e => .store (name a) (expr i) (expr e)
  | .seq c d => .seq (command c) (command d)
  | .ite b c d => .ite (cond b) (command c) (command d)
  | .while b c => .while (cond b) (command c)
  | .read x => read x
  | .write e => .write (expr e)

@[simp] theorem expr_size (e : Expr) : (expr e).size = e.size := by
  induction e <;> simp_all [expr, Expr.size]

@[simp] theorem cond_size (b : Cond) : (cond b).size = b.size := by
  cases b <;> simp [cond, Cond.size]

structure Rel (xs : List ℕ) (σ τ : Env) : Prop where
  vars : ∀ x, τ.vars (name x) = σ.vars x
  arrs : ∀ a, τ.arrs (name a) = σ.arrs a
  out : τ.out = σ.out
  buffer : τ.arrs "" = xs
  cursor : τ.vars "" ≤ xs.length
  inp : σ.inp = xs.drop (τ.vars "")

theorem eval {xs : List ℕ} {σ τ : Env} (h : Rel xs σ τ) {B B' : ℕ}
    (hB : B ≤ B') {e : Expr} {v : ℕ} (he : e.evalB B σ = some v) :
    (expr e).evalB B' τ = some v := by
  induction e generalizing v with
  | lit n =>
    obtain ⟨rfl, hn⟩ := evalB_lit_iff.mp he
    exact evalB_lit (hn.trans_le hB)
  | var x =>
    obtain ⟨rfl, hx⟩ := evalB_var_iff.mp he
    rw [expr, evalB_var_iff, h.vars]
    exact ⟨rfl, hx.trans_le hB⟩
  | get a i ih =>
    obtain ⟨j, hj, hv, hlt⟩ := evalB_get_iff.mp he
    rw [expr, evalB_get_iff]
    exact ⟨j, ih hj, by rwa [h.arrs], hlt.trans_le hB⟩
  | bin op e f ihe ihf =>
    obtain ⟨m, n, hm, hn, rfl, hlt⟩ := evalB_bin_iff.mp he
    exact evalB_bin (ihe hm) (ihf hn) (hlt.trans_le hB)

theorem eval_cond {xs : List ℕ} {σ τ : Env} (h : Rel xs σ τ) {B B' : ℕ}
    (hB : B ≤ B') {b : Cond} {v : Bool} (hb : b.evalB B σ = some v) :
    (cond b).evalB B' τ = some v := by
  cases b with
  | eq e f =>
    obtain ⟨m, hm, n, hn, rfl⟩ := (by
      simpa only [Cond.evalB, Option.bind_eq_some_iff, Option.map_eq_some_iff] using hb :
      ∃ m, e.evalB B σ = some m ∧ ∃ n, f.evalB B σ = some n ∧ (m == n) = v)
    exact evalB_condEq (eval h hB hm) (eval h hB hn)
  | lt e f =>
    obtain ⟨m, hm, n, hn, rfl⟩ := (by
      simpa only [Cond.evalB, Option.bind_eq_some_iff, Option.map_eq_some_iff] using hb :
      ∃ m, e.evalB B σ = some m ∧ ∃ n, f.evalB B σ = some n ∧ decide (m < n) = v)
    exact evalB_condLt (eval h hB hm) (eval h hB hn)

theorem Rel.setVar {xs : List ℕ} {σ τ : Env} (h : Rel xs σ τ) (x : String) (v : ℕ) :
    Rel xs (σ.setVar x v) (τ.setVar (name x) v) := by
  refine ⟨?_, h.arrs, h.out, h.buffer, ?_, ?_⟩
  · intro y
    simp [vars_setVar, h.vars]
  · simpa using h.cursor
  · simpa using h.inp

theorem Rel.setArr {xs : List ℕ} {σ τ : Env} (h : Rel xs σ τ) (a : String) (i v : ℕ) :
    Rel xs (σ.setArr a i v) (τ.setArr (name a) i v) := by
  refine ⟨h.vars, ?_, h.out, ?_, h.cursor, h.inp⟩
  · intro b
    simp [arrs_setArr, h.arrs]
  · simpa using h.buffer

theorem Rel.write {xs : List ℕ} {σ τ : Env} (h : Rel xs σ τ) (v : ℕ) :
    Rel xs {σ with out := σ.out ++ [v]} {τ with out := τ.out ++ [v]} := by
  exact ⟨h.vars, h.arrs, by simp [h.out], h.buffer, h.cursor, h.inp⟩

theorem read_run {xs : List ℕ} {σ τ : Env} (h : Rel xs σ τ) {B : ℕ}
    (hlen : xs.length < B) (hwords : ∀ v ∈ xs, v < B)
    {x : String} {v : ℕ} {rest : List ℕ} (hinp : σ.inp = v::rest) :
    ∃ τ', Run B (read x) τ τ' 7 ∧ Rel xs {σ.setVar x v with inp := rest} τ' := by
  have hd : xs.drop (τ.vars "") = v::rest := h.inp.symm.trans hinp
  have hi : τ.vars "" < xs.length := by
    by_contra hn
    rw [List.drop_eq_nil_iff.mpr (by omega)] at hd
    contradiction
  have hg : xs[τ.vars ""]? = some v := by
    have hh := congrArg (fun ys : List ℕ => ys.head?) hd
    simpa using hh
  have hv : v < B := hwords v (List.mem_of_getElem? hg)
  have hget : (Expr.get "" (.var "")).evalB B τ = some v := by
    rw [evalB_get_iff]
    exact ⟨τ.vars "", evalB_var (hi.trans hlen), by rwa [h.buffer], hv⟩
  let μ := τ.setVar (name x) v
  let τ' := μ.setVar "" (τ.vars ""+1)
  have r1 : Run B (.assign (name x) (.get "" (.var ""))) τ μ 3 := Run.assign hget
  have he : (Expr.add (.var "") (.lit 1)).evalB B μ = some (τ.vars ""+1) := by
    apply evalB_bin (op := .add)
    · rw [evalB_var_iff]
      exact ⟨by simp [μ], by simp [μ]; omega⟩
    · exact evalB_lit (by omega)
    · change τ.vars ""+1 < B
      omega
  have r2 : Run B (.assign "" (.add (.var "") (.lit 1))) μ τ' 4 := Run.assign he
  refine ⟨τ', r1.seq r2, ?_⟩
  refine ⟨?_, h.arrs, h.out, h.buffer, ?_, ?_⟩
  · intro y
    simp [τ', μ, h.vars]
  · simp only [τ', vars_setVar, if_true]
    omega
  · simp only [τ', vars_setVar, if_true]
    have hh := congrArg List.tail hd
    simpa only [List.tail_drop, List.tail_cons] using hh.symm

/-- Redirecting reads costs at most a factor of eight in the structured model. -/
theorem bigStep {B : ℕ} {c : Com} {σ σ' : Env} {t : ℕ}
    (run : BigStepB B c σ σ' t) {B' : ℕ} (hB : B ≤ B')
    {xs : List ℕ} (hlen : xs.length < B') (hwords : ∀ v ∈ xs, v < B')
    {τ : Env} (h : Rel xs σ τ) :
    ∃ τ', Run B' (command c) τ τ' (8*t) ∧ Rel xs σ' τ' := by
  induction run generalizing τ with
  | skip => exact ⟨τ, Run.skip.mono (by omega), h⟩
  | assign he =>
    exact ⟨_, (Run.assign (eval h hB he)).mono (by simp <;> omega), h.setVar _ _⟩
  | store hi he hk =>
    exact ⟨_, (Run.store (eval h hB hi) (eval h hB he) (by rwa [h.arrs])).mono
      (by simp <;> omega), h.setArr _ _ _⟩
  | seq r1 r2 ih1 ih2 =>
    obtain ⟨μ, rr1, hh1⟩ := ih1 h
    obtain ⟨ν, rr2, hh2⟩ := ih2 hh1
    exact ⟨ν, (rr1.seq rr2).mono (by omega), hh2⟩
  | ite_true hb hc ih =>
    obtain ⟨ν, rr, hh⟩ := ih h
    exact ⟨ν, (rr.ite_true (eval_cond h hB hb)).mono (by simp; omega), hh⟩
  | ite_false hb hc ih =>
    obtain ⟨ν, rr, hh⟩ := ih h
    exact ⟨ν, (rr.ite_false (eval_cond h hB hb)).mono (by simp; omega), hh⟩
  | while_true hb hc hw ihc ihw =>
    obtain ⟨μ, ⟨t1, ht1, r1⟩, hh1⟩ := ihc h
    obtain ⟨ν, ⟨t2, ht2, r2⟩, hh2⟩ := ihw hh1
    refine ⟨ν, ⟨_, ?_, BigStepB.while_true (eval_cond h hB hb) r1 r2⟩, hh2⟩
    simp only [cond_size]
    omega
  | while_false hb =>
    exact ⟨τ, (Run.while_false (eval_cond h hB hb)).mono (by simp <;> omega), h⟩
  | read hinp =>
    obtain ⟨ν, rr, hh⟩ := read_run h hlen hwords hinp
    exact ⟨ν, rr.mono (by omega), hh⟩
  | write he =>
    exact ⟨_, (Run.write (eval h hB he)).mono (by simp <;> omega), h.write _⟩

theorem run {B B' : ℕ} {c : Com} {σ σ' : Env} {t : ℕ}
    (hr : Run B c σ σ' t) (hB : B ≤ B')
    {xs : List ℕ} (hlen : xs.length < B') (hwords : ∀ v ∈ xs, v < B')
    {τ : Env} (h : Rel xs σ τ) :
    ∃ τ', Run B' (command c) τ τ' (8*t) ∧ Rel xs σ' τ' := by
  obtain ⟨s, hs, hr⟩ := hr
  obtain ⟨τ', ht, hh⟩ := bigStep hr hB hlen hwords h
  exact ⟨τ', ht.mono (Nat.mul_le_mul_left _ hs), hh⟩

end Lax263307Proofs.BufferedCommand
