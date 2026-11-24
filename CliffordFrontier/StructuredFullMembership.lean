/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.FullMembership
public import CliffordFrontier.Reductions
public import CliffordFrontier.StructuredMembership
public import CslibFrontier.Computability.Complexity.Classes.NP.Closure

/-!
# Structured Full Membership

NP membership for block-diagonal tableau synthesis and its structured restrictions.
-/

public section

namespace CliffordFrontier

open Cslib.Complexity CliffordSynthesis

theorem freeSwaps_mem_NP : synthesisWithFreeSwaps ∈ NP encSynthesisInput :=
  to_full_free_swaps.mem_NP fullFreeSwaps_mem_NP

theorem gateFamily_mem_NP (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    gateFamilySynthesis Γ ∈ NP encSynthesisInput :=
  (to_full_gate_family Γ).mem_NP (fullGateFamily_mem_NP Γ supports)

theorem gateFamilyFreeSwaps_mem_NP (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    gateFamilySynthesisWithFreeSwaps Γ ∈ NP encSynthesisInput :=
  (to_full_gate_family_free_swaps Γ).mem_NP (fullGateFamilyFreeSwaps_mem_NP Γ supports)

theorem structuredFreeSwaps_mem_NP :
    structuredTargets ∩ synthesisWithFreeSwaps ∈ NP encSynthesisInput :=
  inter_mem_NP structuredTargets_mem_NP freeSwaps_mem_NP

theorem structuredGateFamily_mem_NP (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    structuredTargets ∩ gateFamilySynthesis Γ ∈ NP encSynthesisInput :=
  inter_mem_NP structuredTargets_mem_NP (gateFamily_mem_NP Γ supports)

theorem structuredGateFamilyFreeSwaps_mem_NP (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    structuredTargets ∩ gateFamilySynthesisWithFreeSwaps Γ ∈ NP encSynthesisInput :=
  inter_mem_NP structuredTargets_mem_NP (gateFamilyFreeSwaps_mem_NP Γ supports)

end CliffordFrontier
