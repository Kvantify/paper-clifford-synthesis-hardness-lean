/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.Membership
public import CliffordFrontier.Reductions -- shake: keep
public import CliffordFrontier.SignedReduction
import CliffordFrontier.SignedMembership
import CliffordFrontier.StructuredFullMembership
import CliffordFrontier.StructuredSignedMembership
import GridHardness.SatCompiledGridReduction

/-!
# NP-completeness of Clifford synthesis

Compose the grid hardness theorem with the tableau reductions and pair each hardness theorem
with its polynomial verifier. The gate-family results assume local Clifford equivalence to
CNOT. The signed results require an available CNOT and a positive two-qubit gate weight.

## Main results

* `clifford_npComplete` and `cnotOnly_npComplete` cover block-diagonal input.
* `structuredClifford_npComplete` covers the three-block restriction.
* `fullClifford_npComplete` and `fullGateFamily_npComplete` cover dense symplectic input.
* `signed_npComplete` covers dense signed input with fixed gate weights.

## References

* [FugledeJorgensen2026]
-/

public section

namespace CliffordFrontier

open Cslib.Complexity CliffordComplexity CliffordSynthesis

/-- Specified-endpoint Hamiltonian path on finite induced grid graphs is NP-hard. -/
theorem gridHamiltonian_npHard : NPHard encGridInput gridHamiltonian :=
  positiveExactOne_npHard.trans GridHardness.SatCompiledGridReduction.positivePath.polyTimeReducible

/-- Phase-free CNOT-count synthesis for block-diagonal targets is NP-complete. -/
theorem clifford_npComplete : NPComplete encSynthesisInput cliffordSynthesis :=
  ⟨clifford_mem_NP, gridHamiltonian_npHard.trans grid_to_clifford⟩

/-- CNOT-only synthesis for block-diagonal targets is NP-complete. -/
theorem cnotOnly_npComplete : NPComplete encSynthesisInput cnotOnlySynthesis :=
  ⟨cnotOnly_mem_NP, gridHamiltonian_npHard.trans grid_to_cnot_only⟩

/-- Phase-free CNOT-count synthesis for block-diagonal targets with free SWAPs is NP-hard. -/
theorem freeSwaps_npHard : NPHard encSynthesisInput synthesisWithFreeSwaps :=
  gridHamiltonian_npHard.trans grid_to_free_swaps

/-- Phase-free CNOT-count synthesis for block-diagonal targets with free SWAPs is NP-complete. -/
theorem freeSwaps_npComplete : NPComplete encSynthesisInput synthesisWithFreeSwaps :=
  ⟨freeSwaps_mem_NP, freeSwaps_npHard⟩

/-- Phase-free synthesis for block-diagonal targets
with a fixed two-qubit gate family is NP-hard. -/
theorem gateFamily_npHard (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encSynthesisInput (gateFamilySynthesis Γ) :=
  gridHamiltonian_npHard.trans (grid_to_gate_family Γ supports)

/-- Phase-free synthesis for block-diagonal targets
with a fixed two-qubit gate family is NP-complete. -/
theorem gateFamily_npComplete (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encSynthesisInput (gateFamilySynthesis Γ) :=
  ⟨gateFamily_mem_NP Γ supports, gateFamily_npHard Γ supports⟩

/-- Phase-free synthesis for block-diagonal targets
with a fixed gate family and free SWAPs is NP-hard. -/
theorem gateFamilyFreeSwaps_npHard (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encSynthesisInput (gateFamilySynthesisWithFreeSwaps Γ) :=
  gridHamiltonian_npHard.trans (grid_to_gate_family_free_swaps Γ supports)

/-- Phase-free synthesis for block-diagonal targets
with a fixed gate family and free SWAPs is NP-complete. -/
theorem gateFamilyFreeSwaps_npComplete (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encSynthesisInput (gateFamilySynthesisWithFreeSwaps Γ) :=
  ⟨gateFamilyFreeSwaps_mem_NP Γ supports, gateFamilyFreeSwaps_npHard Γ supports⟩

/-- Phase-free CNOT-count synthesis for three-block targets is NP-hard. -/
theorem structuredClifford_npHard :
    NPHard encSynthesisInput (structuredTargets ∩ cliffordSynthesis) :=
  gridHamiltonian_npHard.trans grid_to_structured_clifford

/-- Phase-free CNOT-count synthesis for three-block targets is NP-complete. -/
theorem structuredClifford_npComplete :
    NPComplete encSynthesisInput (structuredTargets ∩ cliffordSynthesis) :=
  ⟨inter_mem_NP structuredTargets_mem_NP clifford_mem_NP, structuredClifford_npHard⟩

/-- Phase-free CNOT-count synthesis for three-block targets with free SWAPs is NP-hard. -/
theorem structuredFreeSwaps_npHard :
    NPHard encSynthesisInput (structuredTargets ∩ synthesisWithFreeSwaps) :=
  gridHamiltonian_npHard.trans grid_to_structured_free_swaps

/-- Phase-free CNOT-count synthesis for three-block targets with free SWAPs is NP-complete. -/
theorem structuredFreeSwaps_npComplete :
    NPComplete encSynthesisInput (structuredTargets ∩ synthesisWithFreeSwaps) :=
  ⟨structuredFreeSwaps_mem_NP, structuredFreeSwaps_npHard⟩

/-- Phase-free synthesis for three-block targets
with a fixed two-qubit gate family is NP-hard. -/
theorem structuredGateFamily_npHard (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encSynthesisInput (structuredTargets ∩ gateFamilySynthesis Γ) :=
  gridHamiltonian_npHard.trans (grid_to_structured_gate_family Γ supports)

/-- Phase-free synthesis for three-block targets
with a fixed two-qubit gate family is NP-complete. -/
theorem structuredGateFamily_npComplete (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encSynthesisInput (structuredTargets ∩ gateFamilySynthesis Γ) :=
  ⟨structuredGateFamily_mem_NP Γ supports, structuredGateFamily_npHard Γ supports⟩

/-- Phase-free synthesis for three-block targets
with a fixed gate family and free SWAPs is NP-hard. -/
theorem structuredGateFamilyFreeSwaps_npHard (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encSynthesisInput (structuredTargets ∩ gateFamilySynthesisWithFreeSwaps Γ) :=
  gridHamiltonian_npHard.trans (grid_to_structured_gate_family_free_swaps Γ supports)

/-- Phase-free synthesis for three-block targets
with a fixed gate family and free SWAPs is NP-complete. -/
theorem structuredGateFamilyFreeSwaps_npComplete (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encSynthesisInput (structuredTargets ∩ gateFamilySynthesisWithFreeSwaps Γ) :=
  ⟨structuredGateFamilyFreeSwaps_mem_NP Γ supports, structuredGateFamilyFreeSwaps_npHard Γ supports⟩

/-- Phase-free CNOT-count synthesis for full symplectic tableaux is NP-hard. -/
theorem fullClifford_npHard : NPHard encFullTableauInput fullCliffordSynthesis :=
  clifford_npComplete.2.trans to_full_clifford

/-- Phase-free CNOT-count synthesis for full symplectic tableaux is NP-complete. -/
theorem fullClifford_npComplete : NPComplete encFullTableauInput fullCliffordSynthesis :=
  ⟨fullClifford_mem_NP, fullClifford_npHard⟩

/-- Phase-free CNOT-count synthesis for full symplectic tableaux with free SWAPs is NP-hard. -/
theorem fullFreeSwaps_npHard : NPHard encFullTableauInput fullSynthesisWithFreeSwaps :=
  freeSwaps_npHard.trans to_full_free_swaps

/-- Phase-free CNOT-count synthesis for full symplectic tableaux with free SWAPs is NP-complete. -/
theorem fullFreeSwaps_npComplete : NPComplete encFullTableauInput fullSynthesisWithFreeSwaps :=
  ⟨fullFreeSwaps_mem_NP, fullFreeSwaps_npHard⟩

/-- Phase-free synthesis for full symplectic tableaux
with a fixed two-qubit gate family is NP-hard. -/
theorem fullGateFamily_npHard (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encFullTableauInput (fullGateFamilySynthesis Γ) :=
  (gateFamily_npHard Γ supports).trans (to_full_gate_family Γ)

/-- Phase-free synthesis for full symplectic tableaux
with a fixed two-qubit gate family is NP-complete. -/
theorem fullGateFamily_npComplete (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encFullTableauInput (fullGateFamilySynthesis Γ) :=
  ⟨fullGateFamily_mem_NP Γ supports, fullGateFamily_npHard Γ supports⟩

/-- Phase-free synthesis for full symplectic tableaux
with a fixed gate family and free SWAPs is NP-hard. -/
theorem fullGateFamilyFreeSwaps_npHard (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encFullTableauInput (fullGateFamilySynthesisWithFreeSwaps Γ) :=
  (gateFamilyFreeSwaps_npHard Γ supports).trans (to_full_gate_family_free_swaps Γ)

/-- Phase-free synthesis for full symplectic tableaux
with a fixed gate family and free SWAPs is NP-complete. -/
theorem fullGateFamilyFreeSwaps_npComplete (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encFullTableauInput (fullGateFamilySynthesisWithFreeSwaps Γ) :=
  ⟨fullGateFamilyFreeSwaps_mem_NP Γ supports, fullGateFamilyFreeSwaps_npHard Γ supports⟩

/-- Weighted synthesis for full signed tableaux is NP-hard. -/
theorem signed_npHard (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    NPHard encSignedInput (signedSynthesis Γ a b freeSwaps) :=
  gridHamiltonian_npHard.trans (grid_to_signed Γ a b hb hΓ freeSwaps)

/-- Weighted synthesis for full signed tableaux is NP-complete. -/
theorem signed_npComplete (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    NPComplete encSignedInput (signedSynthesis Γ a b freeSwaps) :=
  ⟨signed_mem_NP Γ a b hb hΓ freeSwaps, signed_npHard Γ a b hb hΓ freeSwaps⟩

/-- Weighted synthesis for three-block targets with zero generator signs is NP-hard. -/
theorem structuredSigned_npHard (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    NPHard encSignedInput (structuredSignedTargets b ∩ signedSynthesis Γ a b freeSwaps) :=
  gridHamiltonian_npHard.trans (grid_to_structured_signed Γ a b hb hΓ freeSwaps)

/-- Weighted synthesis for three-block targets with zero generator signs is NP-complete. -/
theorem structuredSigned_npComplete (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    NPComplete encSignedInput (structuredSignedTargets b ∩ signedSynthesis Γ a b freeSwaps) :=
  ⟨inter_mem_NP (structuredSignedTargets_mem_NP b hb) (signed_mem_NP Γ a b hb hΓ freeSwaps),
    structuredSigned_npHard Γ a b hb hΓ freeSwaps⟩

end CliffordFrontier
