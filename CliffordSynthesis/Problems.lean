/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.GridInstance
public import CliffordComplexity.Reduction

/-!
# Problems

Binary encodings and acceptance predicates for the two synthesis problems.
The decoder reads the full X/Z tableau and its CNOT threshold. These definitions
contain no encoded reduction program or certified grid-to-synthesis theorem.
-/

@[expose] public section

namespace CliffordSynthesis.MatrixCompiler
open CliffordComplexity

abbrev RowTy := Ty.list .bool
abbrev MatrixTy := Ty.list RowTy
abbrev OutputTy := Ty.pair MatrixTy (Ty.pair MatrixTy .nat)
def readBit (l : List Bool) (i : Nat) : Bool := l[i]?.getD false

def decode (out : OutputTy.denote) : GridInstance.Instance where
  qubits := out.1.length
  tableau := {
    x := fun i p => if p.2 then false else readBit (out.1[i.val]?.getD []) p.1.val
    z := fun i p => if p.2 then readBit (out.2.1[i.val]?.getD []) p.1.val else false }
  threshold := out.2.2

def Accepts (out : OutputTy.denote) : Prop := GridInstance.Accepts (decode out)

end CliffordSynthesis.MatrixCompiler

namespace CliffordSynthesis
open MatrixCompiler

/-- The target decision problem with only elementary CNOT gates allowed.
The complete tableau, including the Z block, must still be implemented. -/
def HasCNOTCircuit (a : GridInstance.Instance) : Prop :=
  ∃ cs : List (RowExtraction.AddGate a.qubits), cs.length ≤ a.threshold ∧
    Circuit.Same (Circuit.run (RowHistory.asCircuit cs) (Circuit.identity a.qubits)) a.tableau

def CNOTOnly (out : OutputTy.denote) : Prop := HasCNOTCircuit (decode out)

end CliffordSynthesis
