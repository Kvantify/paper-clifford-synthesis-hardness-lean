/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.DecisionProblems
public import CliffordSynthesis.SignedCircuit

/-!
# Weighted signed Clifford synthesis decision languages

The word encoding extends the dense phase-free encoding by two lists of generator signs.
The signed gate model assigns one fixed cost per single-qubit gate and another per two-qubit gate.

## Main definitions

* `signedTableau` decodes the tableau and generator signs.
* `signedSynthesis` is the fixed-weight decision language.
* `structuredSignedTargets` consists of the structured targets with zero generator signs
  and budgets multiplied by the two-qubit gate weight.

## References

* [FugledeJorgensen2026]
-/

@[expose] public section

namespace CliffordFrontier

open CliffordComplexity CliffordSynthesis CliffordSynthesis.MatrixCompiler

/-- A full binary tableau, its budget, and the signs on X and Z images. -/
abbrev SignedInputTy := Ty.pair FullTableauTy (Ty.pair RowTy RowTy)
/-- A full tableau instance together with the X and Z generator sign vectors. -/
abbrev SignedInput := SignedInputTy.denote
/-- Encode a full tableau and binary budget followed by both generator sign vectors. -/
abbrev encSignedInput := encodeTy SignedInputTy

/-- Decode the linear part and both generator sign vectors of a signed instance. -/
def signedTableau (x : SignedInput) : SignedCircuit.Tableau (decodeFull x.1).qubits where
  linear := (decodeFull x.1).tableau
  sign := fun (wire, isZ) =>
    let (xSigns, zSigns) := x.2
    readBit (if isZ then zSigns else xSigns) wire.val

/-- Signed synthesis with fixed gate weights and an optional free SWAP operation. -/
def signedSynthesis (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (freeSwaps : Bool) :
    Set SignedInput :=
  {x | SignedCircuit.Synthesizes Γ a b freeSwaps (signedTableau x) (decodeFull x.1).threshold}

/-- Embed a block-diagonal target with zero generator signs and a scaled budget. -/
def withZeroSigns (b : Nat) : SynthesisInput → SignedInput :=
  fun (xx, zz, budget) => (((xx, []), (([], zz), b * budget)), ([], []))

/-- The polynomial-time program that adds zero signs and scales the binary budget. -/
def withZeroSignsCode (b : Nat) : Code OutputTy SignedInputTy :=
  .pair
    (.pair (.pair .fst (.const MatrixTy []))
      (.pair (.pair (.const MatrixTy []) (.comp .snd .fst))
        (.comp (.pair (.const .nat b) (.comp .snd .snd)) .natMul)))
    (.const (.pair RowTy RowTy) ([], []))

/-- The signed embedding program computes the zero-sign, scaled-budget embedding. -/
theorem withZeroSignsCode_eval (b : Nat) : (withZeroSignsCode b).eval = withZeroSigns b := rfl

/-- The zero-sign image of the three-block targets with budgets scaled by the weight. -/
def structuredSignedTargets (b : Nat) : Set SignedInput :=
  withZeroSigns b '' structuredTargets

end CliffordFrontier
