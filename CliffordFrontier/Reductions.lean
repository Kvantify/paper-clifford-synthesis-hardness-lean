/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.DecisionProblems
public import CliffordSynthesis.CNOTOnly
public import CliffordSynthesis.GeneralReduction

/-!
# Grid reductions to phase-free Clifford synthesis

Polynomial-time reductions from specified-endpoint grid Hamiltonian path to block-diagonal
targets, followed by the embedding into dense phase-free tableaus.

## Main results

* `grid_to_clifford`, `grid_to_cnot_only` and `grid_to_free_swaps` cover the CNOT models.
* `grid_to_gate_family` and `grid_to_structured_gate_family` cover fixed gate families.
* `to_full_clifford` and `to_full_gate_family` certify the dense-tableau embedding.

## References

* [FugledeJorgensen2026]
* [LiGuan2026]
-/

@[expose] public section

namespace CliffordFrontier

open Cslib.Complexity CliffordComplexity CliffordSynthesis
open CliffordSynthesis.GridCompiler CliffordSynthesis.MatrixCompiler

/-- Encode a grid instance as a block-diagonal Clifford synthesis problem. -/
theorem grid_to_clifford :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian cliffordSynthesis :=
  certifiedGridToClifford.polyTimeReducible

/-- On the reduction outputs, allowing only CNOTs preserves the grid equivalence. -/
theorem grid_to_cnot_only :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian cnotOnlySynthesis :=
  certifiedGridToCNOTOnly.polyTimeReducible

/-- The grid equivalence survives the addition of free SWAP gates. -/
theorem grid_to_free_swaps :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian synthesisWithFreeSwaps :=
  certifiedGridToFreeSwaps.polyTimeReducible

/-- A locally CNOT-equivalent gate in the family suffices for the grid reduction. -/
theorem grid_to_gate_family (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian (gateFamilySynthesis Γ) :=
  (certifiedGridToGateFamily Γ supports).polyTimeReducible

/-- The fixed-family grid reduction also allows free SWAP gates. -/
theorem grid_to_gate_family_free_swaps (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian
      (gateFamilySynthesisWithFreeSwaps Γ) :=
  (certifiedGridToGateFamilyFreeSwaps Γ supports).polyTimeReducible

/-- The grid reduction outputs the three-block Clifford targets. -/
theorem grid_to_structured_clifford :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian
      (structuredTargets ∩ cliffordSynthesis) :=
  ⟨_, gridToClifford.polyTime, fun x =>
    (gridToClifford_correct x).trans (and_iff_right (gridToClifford_restrictions x)).symm⟩

/-- The three-block grid reduction also allows free SWAPs. -/
theorem grid_to_structured_free_swaps :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian
      (structuredTargets ∩ synthesisWithFreeSwaps) :=
  ⟨_, gridToClifford.polyTime, fun x =>
    (certifiedGridToFreeSwaps.correct x).trans
      (and_iff_right (gridToClifford_restrictions x)).symm⟩

/-- The fixed-family grid reduction yields three-block targets. -/
theorem grid_to_structured_gate_family (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian
      (structuredTargets ∩ gateFamilySynthesis Γ) :=
  ⟨_, gridToClifford.polyTime, fun x =>
    ((certifiedGridToGateFamily Γ supports).correct x).trans
      (and_iff_right (gridToClifford_restrictions x)).symm⟩

/-- The fixed-family reduction yields three-block targets with free SWAPs allowed. -/
theorem grid_to_structured_gate_family_free_swaps (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian
      (structuredTargets ∩ gateFamilySynthesisWithFreeSwaps Γ) :=
  ⟨_, gridToClifford.polyTime, fun x =>
    ((certifiedGridToGateFamilyFreeSwaps Γ supports).correct x).trans
      (and_iff_right (gridToClifford_restrictions x)).symm⟩

/-- Embed a block-diagonal encoding into the full encoding by filling zero blocks. -/
def blockDiagonal : Code OutputTy FullTableauTy :=
  .pair (.pair .fst (.const MatrixTy []))
    (.pair (.pair (.const MatrixTy []) (.comp .snd .fst)) (.comp .snd .snd))

@[simp] theorem decodeFull_blockDiagonal (x : SynthesisInput) :
    decodeFull (blockDiagonal.eval x) = decode x := by
  apply instance_ext (decodeFull (blockDiagonal.eval x)) (decode x) rfl rfl
  · intro i p
    rcases p with ⟨j, b⟩
    cases b <;> rfl
  · intro i p
    rcases p with ⟨j, b⟩
    cases b <;> rfl

private theorem blockDiagonal_reduction (P : GridInstance.Instance → Prop) :
    PolyTimeReducible encSynthesisInput encFullTableauInput
      {x | P (decode x)} {x | P (decodeFull x)} :=
  ⟨_, blockDiagonal.polyTime, fun x => by
    change P (decode x) ↔ P (decodeFull (blockDiagonal.eval x))
    rw [decodeFull_blockDiagonal]⟩

theorem to_full_clifford :
    PolyTimeReducible encSynthesisInput encFullTableauInput
      cliffordSynthesis fullCliffordSynthesis :=
  blockDiagonal_reduction GridInstance.Accepts

theorem to_full_free_swaps :
    PolyTimeReducible encSynthesisInput encFullTableauInput
      synthesisWithFreeSwaps fullSynthesisWithFreeSwaps :=
  blockDiagonal_reduction (fun a => FreeSwaps.Synthesizes a.tableau a.threshold)

theorem to_full_gate_family (Γ : Set TwoQubit.Gate) :
    PolyTimeReducible encSynthesisInput encFullTableauInput
      (gateFamilySynthesis Γ) (fullGateFamilySynthesis Γ) :=
  blockDiagonal_reduction (fun a => TwoQubit.SynthesizesFrom Γ a.tableau a.threshold)

theorem to_full_gate_family_free_swaps (Γ : Set TwoQubit.Gate) :
    PolyTimeReducible encSynthesisInput encFullTableauInput
      (gateFamilySynthesisWithFreeSwaps Γ) (fullGateFamilySynthesisWithFreeSwaps Γ) :=
  blockDiagonal_reduction (fun a => TwoQubit.SynthesizesFromWithFreeSwaps Γ a.tableau a.threshold)

end CliffordFrontier
