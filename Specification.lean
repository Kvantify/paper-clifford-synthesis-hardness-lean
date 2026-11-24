/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.SignedProblem

/-!
# Comparator specification for Clifford synthesis

Lean Comparator builds these statements independently of the proof library.
-/

public section

namespace CliffordFrontier

open Cslib.Complexity CliffordSynthesis

theorem clifford_mem_NP : cliffordSynthesis ∈ NP encSynthesisInput := by sorry

theorem cnotOnly_mem_NP : cnotOnlySynthesis ∈ NP encSynthesisInput := by sorry

theorem grid_to_clifford :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian cliffordSynthesis := by sorry

theorem grid_to_cnot_only :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian cnotOnlySynthesis := by sorry

theorem grid_to_free_swaps :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian synthesisWithFreeSwaps := by
  sorry

theorem grid_to_gate_family (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian (gateFamilySynthesis Γ) := by
  sorry

theorem grid_to_gate_family_free_swaps (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian
      (gateFamilySynthesisWithFreeSwaps Γ) := by sorry

theorem grid_to_structured_clifford :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian
      (structuredTargets ∩ cliffordSynthesis) := by sorry

theorem grid_to_structured_free_swaps :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian
      (structuredTargets ∩ synthesisWithFreeSwaps) := by sorry

theorem grid_to_structured_gate_family (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian
      (structuredTargets ∩ gateFamilySynthesis Γ) := by sorry

theorem grid_to_structured_gate_family_free_swaps (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    PolyTimeReducible encGridInput encSynthesisInput gridHamiltonian
      (structuredTargets ∩ gateFamilySynthesisWithFreeSwaps Γ) := by sorry

theorem gridHamiltonian_npHard : NPHard encGridInput gridHamiltonian := by sorry

theorem clifford_npComplete : NPComplete encSynthesisInput cliffordSynthesis := by sorry

theorem cnotOnly_npComplete : NPComplete encSynthesisInput cnotOnlySynthesis := by sorry

theorem freeSwaps_npHard : NPHard encSynthesisInput synthesisWithFreeSwaps := by sorry

theorem freeSwaps_npComplete : NPComplete encSynthesisInput synthesisWithFreeSwaps := by sorry

theorem gateFamily_npHard (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encSynthesisInput (gateFamilySynthesis Γ) := by sorry

theorem gateFamily_npComplete (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encSynthesisInput (gateFamilySynthesis Γ) := by sorry

theorem gateFamilyFreeSwaps_npHard (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encSynthesisInput (gateFamilySynthesisWithFreeSwaps Γ) := by sorry

theorem gateFamilyFreeSwaps_npComplete (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encSynthesisInput (gateFamilySynthesisWithFreeSwaps Γ) := by sorry

theorem structuredClifford_npHard :
    NPHard encSynthesisInput (structuredTargets ∩ cliffordSynthesis) := by sorry

theorem structuredClifford_npComplete :
    NPComplete encSynthesisInput (structuredTargets ∩ cliffordSynthesis) := by sorry

theorem structuredFreeSwaps_npHard :
    NPHard encSynthesisInput (structuredTargets ∩ synthesisWithFreeSwaps) := by sorry

theorem structuredFreeSwaps_npComplete :
    NPComplete encSynthesisInput (structuredTargets ∩ synthesisWithFreeSwaps) := by sorry

theorem structuredGateFamily_npHard (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encSynthesisInput (structuredTargets ∩ gateFamilySynthesis Γ) := by sorry

theorem structuredGateFamily_npComplete (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encSynthesisInput (structuredTargets ∩ gateFamilySynthesis Γ) := by sorry

theorem structuredGateFamilyFreeSwaps_npHard (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encSynthesisInput (structuredTargets ∩ gateFamilySynthesisWithFreeSwaps Γ) := by sorry

theorem structuredGateFamilyFreeSwaps_npComplete (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encSynthesisInput (structuredTargets ∩ gateFamilySynthesisWithFreeSwaps Γ) := by
  sorry

theorem fullClifford_npHard : NPHard encFullTableauInput fullCliffordSynthesis := by sorry

theorem fullClifford_npComplete : NPComplete encFullTableauInput fullCliffordSynthesis := by sorry

theorem fullFreeSwaps_npHard : NPHard encFullTableauInput fullSynthesisWithFreeSwaps := by sorry

theorem fullFreeSwaps_npComplete : NPComplete encFullTableauInput fullSynthesisWithFreeSwaps := by
  sorry

theorem fullGateFamily_npHard (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encFullTableauInput (fullGateFamilySynthesis Γ) := by sorry

theorem fullGateFamily_npComplete (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encFullTableauInput (fullGateFamilySynthesis Γ) := by sorry

theorem fullGateFamilyFreeSwaps_npHard (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPHard encFullTableauInput (fullGateFamilySynthesisWithFreeSwaps Γ) := by sorry

theorem fullGateFamilyFreeSwaps_npComplete (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    NPComplete encFullTableauInput (fullGateFamilySynthesisWithFreeSwaps Γ) := by sorry

theorem grid_to_signed (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    PolyTimeReducible encGridInput encSignedInput gridHamiltonian
      (signedSynthesis Γ a b freeSwaps) := by sorry

theorem grid_to_structured_signed (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    PolyTimeReducible encGridInput encSignedInput gridHamiltonian
      (structuredSignedTargets b ∩ signedSynthesis Γ a b freeSwaps) := by sorry

theorem signed_npHard (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    NPHard encSignedInput (signedSynthesis Γ a b freeSwaps) := by sorry

theorem signed_npComplete (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    NPComplete encSignedInput (signedSynthesis Γ a b freeSwaps) := by sorry

theorem structuredSigned_npHard (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    NPHard encSignedInput (structuredSignedTargets b ∩ signedSynthesis Γ a b freeSwaps) := by sorry

theorem structuredSigned_npComplete (Γ : Set SignedCircuit.TwoGate) (a b : Nat) (hb : 0 < b)
    (hΓ : SignedCircuit.cnotGate ∈ Γ) (freeSwaps : Bool) :
    NPComplete encSignedInput (structuredSignedTargets b ∩ signedSynthesis Γ a b freeSwaps) := by
  sorry

end CliffordFrontier
