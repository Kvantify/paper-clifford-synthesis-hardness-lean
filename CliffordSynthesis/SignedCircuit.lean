/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.GateProblems
public import Mathlib.Data.ZMod.Basic

/-!
# Signed Circuit

Signed Clifford tableaux record the image of each Pauli generator,
including the sign. Local gates are specified by their binary symplectic
actions and the signs on their X and Z generators.
-/

@[expose] public section

namespace CliffordSynthesis.SignedCircuit

open TwoQubit (Bits)

/-- The signed images of the Pauli generators of an `n`-qubit circuit. -/
structure Tableau (n : Nat) where
  /-- The binary symplectic tableau of the images. -/
  linear : Circuit.Tableau n
  /-- The negative-sign bit for each generator, indexed by wire and X/Z kind. -/
  sign : Fin n × Bool → Bool

variable {n : Nat}

def identity (n : Nat) : Tableau n := ⟨Circuit.identity n, fun _ => false⟩

def Same (a b : Tableau n) : Prop :=
  Circuit.Same a.linear b.linear ∧ ∀ p, a.sign p = b.sign p

/-- The sign added by conjugating a positive Pauli. Multiply generator images
in X₀, Z₀, X₁, Z₁ order and restore the Hermitian Pauli phase convention. -/
def signChange (f : Bits → Bits) (s v : Bits) : Bool :=
  -- A signed Pauli is represented by its X/Z support and the exponent of i.
  let multiply : Bits × ZMod 4 → Bits × ZMod 4 → Bits × ZMod 4 :=
    fun ((ax, az, ax', az'), aq) ((bx, bz, bx', bz'), bq) =>
      ((ax ^^ bx, az ^^ bz, ax' ^^ bx', az' ^^ bz'),
        aq + bq + (if (az && bx) ^^ (az' && bx') then 2 else 0))
  let canonicalPhase : Bits → ZMod 4 := fun (x, z, x', z') =>
    (if x && z then 1 else 0) + (if x' && z' then 1 else 0)
  let one : Bits × ZMod 4 := ((false, false, false, false), 0)
  let image := fun present negative basis =>
    if present then (f basis, canonicalPhase (f basis) + (if negative then 2 else 0)) else one
  let (vx₀, vz₀, vx₁, vz₁) := v
  let (sx₀, sz₀, sx₁, sz₁) := s
  let x₀ := image vx₀ sx₀ (true, false, false, false)
  let z₀ := image vz₀ sz₀ (false, true, false, false)
  let x₁ := image vx₁ sx₁ (false, false, true, false)
  let z₁ := image vz₁ sz₁ (false, false, false, true)
  let (_, phase) := multiply (multiply (multiply x₀ z₀) x₁) z₁
  decide (canonicalPhase v + phase ≠ canonicalPhase (f v))

/-- The 24 single-qubit actions and signs, modulo global scalar phase. -/
abbrev LocalGate := Fin 6 × Bool × Bool

/-- A binary two-qubit Clifford action and four generator signs. -/
abbrev TwoGate := TwoQubit.Gate × Bits

def cnotGate : TwoGate := (TwoQubit.cnotGate, false, false, false, false)

inductive Step (n : Nat) where
  | single (i : Fin n) (g : LocalGate)
  | two (c t : Fin n) (distinct : c ≠ t) (g : TwoGate)
  | swap (i j : Fin n)

def Step.allowed (Γ : Set TwoGate) (freeSwaps : Bool) : Step n → Prop
  | .single _ _ => True
  | .two _ _ _ g => g ∈ Γ
  | .swap _ _ => freeSwaps = true

def Step.weight (a b : Nat) : Step n → Nat
  | .single _ _ => a
  | .two _ _ _ _ => b
  | .swap _ _ => 0

def applyStep : Step n → Tableau n → Tableau n
  | .single i g, T =>
    ⟨FreeLayers.applyFrames (Function.update (fun _ => 0) i g.1) T.linear,
      fun p =>
        let (x, z) := FreeLayers.pair T.linear i p
        T.sign p ^^ signChange (TwoQubit.localAction g.1 0)
          (g.2.1, g.2.2, false, false) (x, z, false, false)⟩
  | .two c t _ g, T =>
    ⟨TwoQubit.update c t (TwoQubit.action g.1.val) T.linear,
      fun p => T.sign p ^^ signChange (TwoQubit.action g.1.val) g.2 (TwoQubit.read c t T.linear p)⟩
  | .swap i j, T => ⟨FreeSwaps.reorder (Equiv.swap i j) T.linear, T.sign⟩

def run : List (Step n) → Tableau n → Tableau n
  | [], T => T
  | g :: gs, T => run gs (applyStep g T)

def cost (a b : Nat) : List (Step n) → Nat
  | [] => 0
  | g :: gs => g.weight a b + cost a b gs

def Synthesizes (Γ : Set TwoGate) (a b : Nat) (freeSwaps : Bool) (target : Tableau n) (k : Nat) : Prop :=
  ∃ gs : List (Step n), (∀ g ∈ gs, g.allowed Γ freeSwaps) ∧ cost a b gs ≤ k ∧
    Same (run gs (identity n)) target

end CliffordSynthesis.SignedCircuit
