/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Std

/-!
# Circuit

Fixed-width, labelled, ancilla-free tableau semantics.
The Boolean flag selects an input X coordinate (false) or Z coordinate (true).
-/

@[expose] public section

namespace CliffordSynthesis.Circuit

abbrev Row (n : Nat) := Fin n × Bool → Bool

/-- Images of the X and Z generators of an `n`-qubit circuit, modulo phase. -/
structure Tableau (n : Nat) where
  /-- The symplectic row for each X generator. -/
  x : Fin n → Row n
  /-- The symplectic row for each Z generator. -/
  z : Fin n → Row n

def identity (n : Nat) : Tableau n where
  x i p := decide (i = p.1) && !p.2
  z i p := decide (i = p.1) && p.2

def hadamard {n : Nat} (i : Fin n) (a : Tableau n) : Tableau n where
  x q p := if q = i then a.z q p else a.x q p
  z q p := if q = i then a.x q p else a.z q p

def phase {n : Nat} (i : Fin n) (a : Tableau n) : Tableau n where
  x := a.x
  z q p := if q = i then a.z q p ^^ a.x q p else a.z q p

def cnot {n : Nat} (c t : Fin n) (a : Tableau n) : Tableau n where
  x q p := if q = t then a.x q p ^^ a.x c p else a.x q p
  z q p := if q = c then a.z q p ^^ a.z t p else a.z q p

inductive Gate (n : Nat) where
  | H (q : Fin n)
  | S (q : Fin n)
  | CX (c t : Fin n) (distinct : c ≠ t)

def applyGate {n : Nat} : Gate n → Tableau n → Tableau n
  | .H q => hadamard q
  | .S q => phase q
  | .CX c t _ => cnot c t

def paid {n : Nat} : Gate n → Nat
  | .H _ => 0
  | .S _ => 0
  | .CX _ _ _ => 1

def cost {n : Nat} : List (Gate n) → Nat
  | [] => 0
  | g :: gs => paid g + cost gs

def run {n : Nat} : List (Gate n) → Tableau n → Tableau n
  | [], a => a
  | g :: gs, a => run gs (applyGate g a)

/-- Pointwise equality avoids any reliance on function extensionality. -/
def Same {n : Nat} (a b : Tableau n) : Prop :=
  ∀ q p, a.x q p = b.x q p ∧ a.z q p = b.z q p

/-- Synthesis with a bound on the number of CNOTs and free H and S gates. -/
def SynthesizesWithin {n : Nat} (target : Tableau n) (k : Nat) : Prop :=
  ∃ gates : List (Gate n), cost gates ≤ k ∧ Same (run gates (identity n)) target

private theorem xorCancel : ∀ a b : Bool, ((a ^^ b) ^^ b) = a := by decide

theorem hadamard_involutive {n : Nat} (i : Fin n) (a : Tableau n) :
    Same (hadamard i (hadamard i a)) a := by
  intro q p
  by_cases h : q = i
  · constructor <;> change (if q = i then _ else _) = _
    · rw [ite_eq_left h]; change (if q = i then _ else _) = _; rw [ite_eq_left h]
    · rw [ite_eq_left h]; change (if q = i then _ else _) = _; rw [ite_eq_left h]
  · constructor <;> change (if q = i then _ else _) = _
    · rw [ite_eq_right h]; change (if q = i then _ else _) = _; rw [ite_eq_right h]
    · rw [ite_eq_right h]; change (if q = i then _ else _) = _; rw [ite_eq_right h]

theorem phase_involutive {n : Nat} (i : Fin n) (a : Tableau n) :
    Same (phase i (phase i a)) a := by
  intro q p
  refine ⟨rfl, ?_⟩
  change (if q = i then (if q = i then _ else _) ^^ _
    else (if q = i then _ else _)) = _
  by_cases h : q = i
  · rw [ite_eq_left h, ite_eq_left h]; exact xorCancel _ _
  · rw [ite_eq_right h, ite_eq_right h]

theorem cnot_involutive {n : Nat} (c t : Fin n) (distinct : c ≠ t)
    (a : Tableau n) : Same (cnot c t (cnot c t a)) a := by
  intro q p
  constructor
  · change (if q = t then (if q = t then _ else _) ^^
      (if c = t then _ else _) else (if q = t then _ else _)) = _
    by_cases h : q = t
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_right distinct]; exact xorCancel _ _
    · rw [ite_eq_right h, ite_eq_right h]
  · change (if q = c then (if q = c then _ else _) ^^
      (if t = c then _ else _) else (if q = c then _ else _)) = _
    by_cases h : q = c
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_right (Ne.symm distinct)]; exact xorCancel _ _
    · rw [ite_eq_right h, ite_eq_right h]

theorem cost_append {n : Nat} (gs hs : List (Gate n)) :
    cost (gs ++ hs) = cost gs + cost hs := by
  induction gs with
  | nil => exact (Nat.zero_add _).symm
  | cons g gs ih =>
    change paid g + cost (gs ++ hs) = (paid g + cost gs) + cost hs
    rw [ih, Nat.add_assoc]

theorem run_append {n : Nat} (gs hs : List (Gate n)) (a : Tableau n) :
    run (gs ++ hs) a = run hs (run gs a) := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => exact ih (applyGate g a)

end CliffordSynthesis.Circuit
