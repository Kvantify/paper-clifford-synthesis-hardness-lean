/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Reduction
public import CliffordSynthesis.EncodedTarget
public import CliffordSynthesis.Encoding
public import CliffordSynthesis.GateProblems
public import GridProblems.Source

/-!
# Phase-free Clifford synthesis decision languages

The encodings represent dense Boolean rows and binary budgets. The block-diagonal encoding
stores the XX and ZZ blocks. The full encoding stores all four blocks, and the number of
XX rows is the qubit count. Missing entries decode to zero.

## Main definitions

* `cliffordSynthesis` and `cnotOnlySynthesis` are the block-diagonal decision languages.
* `decodeFull` decodes a dense phase-free tableau and its budget.
* `fullCliffordSynthesis` and `fullGateFamilySynthesis` are full-tableau languages.
* `structuredTargets` describes the three-block targets of [FugledeJorgensen2026].
-/

@[expose] public section

namespace CliffordFrontier

open CliffordComplexity CliffordSynthesis CliffordSynthesis.MatrixCompiler

/-- The dense XX and ZZ blocks and binary budget of a block-diagonal target. -/
abbrev SynthesisInput := OutputTy.denote
/-- Encode the two dense Boolean blocks and the binary budget. -/
abbrev encSynthesisInput := encodeTy OutputTy
/-- Encode the grid coordinates and specified endpoint in binary. -/
abbrev encGridInput := encodeTy GridProblems.GridCode.InputTy

/-- The specified-endpoint Hamiltonian path language on induced grid graphs. -/
def gridHamiltonian : Set GridProblems.GridCode.InputTy.denote :=
  {x | GridProblems.GRID_HAMILTONIAN_PATH x}

/-- Phase-free synthesis with free single-qubit gates and budgeted CNOTs. -/
def cliffordSynthesis : Set SynthesisInput := {x | Accepts x}
/-- Synthesis with CNOTs as the only allowed gates. -/
def cnotOnlySynthesis : Set SynthesisInput := {x | CNOTOnly x}
/-- Phase-free synthesis with budgeted CNOTs and free SWAPs. -/
def synthesisWithFreeSwaps : Set SynthesisInput := {x | WithFreeSwaps x}
/-- Block-diagonal target synthesis with a fixed two-qubit gate family. -/
def gateFamilySynthesis (Γ : Set TwoQubit.Gate) : Set SynthesisInput := {x | WithTwoQubitGates Γ x}
/-- Block-diagonal target synthesis with a fixed gate family and free SWAPs. -/
def gateFamilySynthesisWithFreeSwaps (Γ : Set TwoQubit.Gate) : Set SynthesisInput :=
  {x | WithTwoQubitGatesAndFreeSwaps Γ x}

/-- The XX, XZ, ZX and ZZ blocks of a symplectic tableau and a binary budget. -/
abbrev FullTableauTy := Ty.pair (Ty.pair MatrixTy MatrixTy)
  (Ty.pair (Ty.pair MatrixTy MatrixTy) .nat)

/-- A phase-free synthesis instance with all four blocks supplied explicitly. -/
abbrev FullTableauInput := FullTableauTy.denote
/-- Encode the four dense Boolean blocks and the binary budget. -/
abbrev encFullTableauInput := encodeTy FullTableauTy

/-- Decode all four blocks. The width is the number of rows of the XX block. -/
def decodeFull (out : FullTableauInput) : GridInstance.Instance where
  qubits := (Prod.fst ∘ Prod.fst) out |>.length
  tableau := {
    x := fun i (j, isZ) =>
      let (xx, xz) := out.1
      readBit ((if isZ then xz else xx)[i.val]?.getD []) j.val
    z := fun i (j, isZ) =>
      let ((zx, zz), _) := out.2
      readBit ((if isZ then zz else zx)[i.val]?.getD []) j.val }
  threshold := (Prod.snd ∘ Prod.snd) out

/-- CNOT-count synthesis for full phase-free tableaux. -/
def fullCliffordSynthesis : Set FullTableauInput :=
  {x | GridInstance.Accepts (decodeFull x)}

/-- CNOT-count synthesis for full phase-free tableaux, allowing free SWAPs. -/
def fullSynthesisWithFreeSwaps : Set FullTableauInput :=
  {x | FreeSwaps.Synthesizes (decodeFull x).tableau (decodeFull x).threshold}

/-- Full phase-free tableau synthesis using a fixed two-qubit gate family. -/
def fullGateFamilySynthesis (Γ : Set TwoQubit.Gate) : Set FullTableauInput :=
  {x | TwoQubit.SynthesizesFrom Γ (decodeFull x).tableau (decodeFull x).threshold}

/-- Full phase-free synthesis with a fixed gate family and free SWAPs. -/
def fullGateFamilySynthesisWithFreeSwaps (Γ : Set TwoQubit.Gate) : Set FullTableauInput :=
  {x | TwoQubit.SynthesizesFromWithFreeSwaps Γ (decodeFull x).tableau (decodeFull x).threshold}

/-- The three-block targets, with their matrix properties in physical wire order. -/
def structuredTargets : Set SynthesisInput :=
  {out | ∃ (d r : Nat) (t : Fin d → Planes.F) (X : Matrix (Fin r) (Fin d) Planes.F) (k : Nat),
    out = encode (EncodedTarget.tableau (EncodedTarget.physicalLabel d r) t X) k ∧
    (Target.matrix t X - 1) ^ 3 = 0 ∧
    (∀ i, Target.matrix t X i i = 1) ∧
    (∀ i j, Target.position i < Target.position j → Target.matrix t X i j = 0) ∧
    Target.lift t X ∈ Matrix.symplecticGroup (Target.Wire d r) Planes.F}

end CliffordFrontier
