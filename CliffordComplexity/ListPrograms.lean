/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordComplexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# List Programs

Polynomial-time list programs for filtering with an environment, preserving labels and
looking up the first position of a label.
-/

@[expose] public section

namespace CliffordComplexity
open Turing.MultiTapeTM

namespace Code
variable {s t e : Ty}

/-- Exchange the components of an encoded pair. -/
def swap : Code (.pair s t) (.pair t s) := .pair .snd .fst

/-- Test equality of two pairs of binary natural numbers. -/
def natPairEq : Code (.pair (.pair .nat .nat) (.pair .nat .nat)) .bool :=
  and (.comp (.pair (.comp .fst .fst) (.comp .snd .fst)) .natEq)
      (.comp (.pair (.comp .fst .snd) (.comp .snd .snd)) .natEq)

/-- Retain list elements passing the test and map them using the common environment. -/
def filterMapEnv (test : Code (.pair e s) .bool) (f : Code (.pair e s) t) :
    Code (.pair e (.list s)) (.list t) :=
  .comp (.listMapEnv (.branch test (.comp f .listSingle) (.const (.list t) []))) .listJoin

/-- Filter a list using a test with access to a common environment. -/
def filterEnv (test : Code (.pair e t) .bool) : Code (.pair e (.list t)) (.list t) :=
  filterMapEnv test .snd

/-- First position of a binary natural label, or the list length. -/
def labelIndex : Code (.pair (.list .nat) .nat) .nat :=
  .ofPolyTime (fun x => x.1.idxOf x.2)
    ((ComputableInPolyTime.idxOf encNat).trans ComputableInPolyTime.unary_to_binary)

end Code

theorem branch_eval_true {s t : Ty} {b : Code s .bool} (f g : Code s t) {x : s.denote}
    (h : b.eval x = true) : (Code.branch b f g).eval x = f.eval x := by
  simp [Code.eval, h]

theorem branch_eval_false {s t : Ty} {b : Code s .bool} (f g : Code s t) {x : s.denote}
    (h : b.eval x = false) : (Code.branch b f g).eval x = g.eval x := by
  simp [Code.eval, h]

theorem natPairEq_eval_true (p q : Nat × Nat) : Code.natPairEq.eval (p, q) = true ↔ p = q := by
  change (decide (p.1 = q.1) && decide (p.2 = q.2)) = true ↔ p = q
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, Prod.ext_iff]

theorem append_eval {s t : Ty} (f g : Code s (.list t)) (x : s.denote) :
    (f.append g).eval x = f.eval x ++ g.eval x := rfl

theorem filterMapEnv_eval {e s t : Ty} (test : Code (.pair e s) .bool)
    (f : Code (.pair e s) t) (env : e.denote) (xs : List s.denote) :
    (test.filterMapEnv f).eval (env, xs) = (xs.filter fun a => test.eval (env, a)).map
      (fun a => f.eval (env, a)) := by
  change (xs.map (fun a => if test.eval (env, a) then [f.eval (env, a)] else [])).flatten = _
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : test.eval (env, x) <;> simp [h, ih]

theorem mem_filterMapEnv_eval {e s t : Ty} (test : Code (.pair e s) .bool)
    (f : Code (.pair e s) t) (env : e.denote) (xs : List s.denote) (y : t.denote) :
    y ∈ (test.filterMapEnv f).eval (env, xs) ↔
      ∃ a ∈ xs, test.eval (env, a) = true ∧ f.eval (env, a) = y := by
  rw [filterMapEnv_eval test f env xs]
  simp only [List.mem_map, List.mem_filter, and_assoc]

theorem filterEnv_eval {e t : Ty} (test : Code (.pair e t) .bool)
    (env : e.denote) (xs : List t.denote) :
    (test.filterEnv).eval (env, xs) = xs.filter (fun a => test.eval (env, a)) := by
  rw [Code.filterEnv, filterMapEnv_eval]
  exact List.map_id _

theorem mem_cross_eval {σ τ : Ty} (xs : List σ.denote) (ys : List τ.denote)
    (p : σ.denote × τ.denote) :
    p ∈ Code.cross.eval (xs, ys) ↔ p.1 ∈ xs ∧ p.2 ∈ ys := by
  obtain ⟨a, b⟩ := p
  simp [Code.cross, Code.eval, List.mem_flatten, and_left_comm]

theorem length_cross_eval {σ τ : Ty} (xs : List σ.denote) (ys : List τ.denote) :
    ((Code.cross (σ := σ) (τ := τ)).eval (xs, ys)).length = xs.length * ys.length := by
  change (xs.flatMap fun a => ys.map fun b => (a, b)).length = _
  induction xs <;> simp_all [Nat.add_mul, Nat.add_comm]

end CliffordComplexity
