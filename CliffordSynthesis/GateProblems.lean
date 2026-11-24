/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Problems
public import CliffordSynthesis.FreeSwaps
public import CliffordSynthesis.GateFamilies

/-!
# Gate Problems

Acceptance with free SWAPs and with a fixed family of two-qubit gates.
Both predicates use the same dense tableau and threshold encoding.
-/

@[expose] public section

namespace CliffordSynthesis
open MatrixCompiler

namespace TwoQubit

inductive StepWithSwap (n : Nat) where
  | gate (g : Step n)
  | swap (i j : Fin n)

variable {n : Nat}

def StepWithSwap.allowed (Γ : Set Gate) : StepWithSwap n → Prop
  | .gate g => Allowed Γ g
  | .swap _ _ => True

def StepWithSwap.run : List (StepWithSwap n) → Circuit.Tableau n → Circuit.Tableau n
  | [], a => a
  | .gate g :: gs, a => run gs (applyStep g a)
  | .swap i j :: gs, a => run gs (FreeSwaps.reorder (Equiv.swap i j) a)

def StepWithSwap.cost : List (StepWithSwap n) → Nat
  | [] => 0
  | .gate g :: gs => paid g + cost gs
  | .swap _ _ :: gs => cost gs

def SynthesizesFromWithFreeSwaps (Γ : Set Gate) (target : Circuit.Tableau n) (k : Nat) : Prop :=
  ∃ gs : List (StepWithSwap n), (∀ g ∈ gs, g.allowed Γ) ∧ StepWithSwap.cost gs ≤ k ∧
    Circuit.Same (StepWithSwap.run gs (Circuit.identity n)) target

end TwoQubit

def WithFreeSwaps (out : OutputTy.denote) : Prop :=
  FreeSwaps.Synthesizes (decode out).tableau (decode out).threshold

def WithTwoQubitGates (Γ : Set TwoQubit.Gate) (out : OutputTy.denote) : Prop :=
  TwoQubit.SynthesizesFrom Γ (decode out).tableau (decode out).threshold

def WithTwoQubitGatesAndFreeSwaps (Γ : Set TwoQubit.Gate) (out : OutputTy.denote) : Prop :=
  TwoQubit.SynthesizesFromWithFreeSwaps Γ (decode out).tableau (decode out).threshold

end CliffordSynthesis
