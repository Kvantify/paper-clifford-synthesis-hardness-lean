/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Problems

/-!
# Capped

Both synthesis problems restricted to thresholds at most the qubit count.
-/

@[expose] public section

namespace CliffordFrontier

open CliffordSynthesis CliffordSynthesis.MatrixCompiler

/-- The binary threshold is at most the number of explicitly listed X rows. -/
def WithinQubits (out : OutputTy.denote) : Prop :=
  (decode out).threshold ≤ (decode out).qubits

/-- Clifford synthesis with a budget at most the qubit count. -/
def CappedClifford (out : OutputTy.denote) : Prop := Accepts out ∧ WithinQubits out

/-- CNOT-only synthesis with a budget at most the qubit count. -/
def CappedCNOTOnly (out : OutputTy.denote) : Prop := CNOTOnly out ∧ WithinQubits out

end CliffordFrontier
