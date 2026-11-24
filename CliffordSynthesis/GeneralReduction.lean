/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.GateProblems
public import CliffordSynthesis.SwapsReduction
public import CliffordSynthesis.Restricted

/-!
# General Reduction

Certified reductions for the alternative gate libraries.
-/

@[expose] public section

open GridProblems GridProblems.GridCode

namespace CliffordSynthesis

open CliffordComplexity
open MatrixCompiler GridProblems.GridCode GridCompiler

theorem twoQubit_on_outputs (Γ : Set TwoQubit.Gate) (hΓ : TwoQubit.SupportsCNOT Γ)
    (x : InputTy.denote) :
    WithTwoQubitGates Γ (gridToClifford.eval x) ↔ Accepts (gridToClifford.eval x) := by
  constructor
  · rintro ⟨gs, _, hc, hs⟩
    apply (freeSwaps_on_outputs x).mp
    exact TwoQubit.synthesis_to_freeSwaps _ _ ⟨gs, hc, hs⟩
  · exact TwoQubit.from_circuit Γ hΓ _ _

/-- A certified reduction for any fixed family Γ of
two-qubit Clifford symplectic maps containing a locally CNOT-equivalent gate. -/
def certifiedGridToGateFamily (Γ : Set TwoQubit.Gate) (hΓ : TwoQubit.SupportsCNOT Γ) :
    CertifiedReduction GRID_HAMILTONIAN_PATH (WithTwoQubitGates Γ) where
  code := gridToClifford
  correct x := (gridToClifford_correct x).trans (twoQubit_on_outputs Γ hΓ x).symm

def certifiedGridToAllTwoQubit : CertifiedReduction GRID_HAMILTONIAN_PATH (WithTwoQubitGates Set.univ) :=
  certifiedGridToGateFamily Set.univ TwoQubit.all_supportsCNOT

def certifiedGridToEntangling :
    CertifiedReduction GRID_HAMILTONIAN_PATH (WithTwoQubitGates {g | TwoQubit.Entangling g}) :=
  certifiedGridToGateFamily _ TwoQubit.entangling_supportsCNOT

/-- The gate-library extension retains the same lower-unitriangular,
cube-nilpotent three-block targets, including rejection branches. -/
def certifiedRestrictedGateFamily (Γ : Set TwoQubit.Gate) (hΓ : TwoQubit.SupportsCNOT Γ) :
    CertifiedReduction GRID_HAMILTONIAN_PATH
      (CliffordComplexity.Problem.restrict (WithTwoQubitGates Γ) ThreeBlock) where
  code := gridToClifford
  correct x := ((certifiedGridToGateFamily Γ hΓ).correct x).trans
    (and_iff_right (gridToClifford_threeBlock x)).symm

namespace TwoQubit.StepWithSwap

variable {n : Nat}

theorem to_cnot (gs : List (StepWithSwap n)) :
    ∃ ss : List (FreeSwaps.Step n), FreeSwaps.count ss ≤ cost gs ∧
      ∀ a, FreeSwaps.execute ss a = run gs a := by
  induction gs with
  | nil => exact ⟨[], le_rfl, fun _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨ss, hc, hr⟩ := ih
    cases g with
    | swap i j => exact ⟨.swap i j :: ss, hc, fun a => hr _⟩
    | gate g =>
      obtain ⟨pre, hp, he⟩ := TwoQubit.to_freeSwaps [g]
      have hp' : FreeSwaps.count pre ≤ paid g := by
        simpa only [TwoQubit.cost, Nat.add_zero] using hp
      refine ⟨pre ++ ss, ?_, ?_⟩
      · rw [FreeSwaps.count_append]
        exact Nat.add_le_add hp' hc
      · intro a
        rw [FreeSwaps.execute_append, he, hr]
        rfl

theorem run_gates (gs : List (Step n)) (a : Circuit.Tableau n) :
    run (gs.map gate) a = TwoQubit.run gs a := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem cost_gates (gs : List (Step n)) : cost (gs.map gate) = TwoQubit.cost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => exact congrArg (paid g + ·) ih

end TwoQubit.StepWithSwap

theorem gateFamilyFreeSwaps_on_outputs (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) (x : InputTy.denote) :
    WithTwoQubitGatesAndFreeSwaps Γ (gridToClifford.eval x) ↔ Accepts (gridToClifford.eval x) := by
  constructor
  · rintro ⟨gs, _, hc, hs⟩
    obtain ⟨ss, hsc, hr⟩ := TwoQubit.StepWithSwap.to_cnot gs
    exact (freeSwaps_on_outputs x).mp ⟨ss, hsc.trans hc, by rwa [hr]⟩
  · intro h
    obtain ⟨gs, ha, hc, hs⟩ := TwoQubit.from_circuit Γ supports _ _ h
    refine ⟨gs.map .gate, ?_, by rwa [TwoQubit.StepWithSwap.cost_gates],
      by rwa [TwoQubit.StepWithSwap.run_gates]⟩
    intro step hstep
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hstep
    exact ha g hg

def certifiedGridToGateFamilyFreeSwaps (Γ : Set TwoQubit.Gate)
    (supports : TwoQubit.SupportsCNOT Γ) :
    CertifiedReduction GRID_HAMILTONIAN_PATH (WithTwoQubitGatesAndFreeSwaps Γ) where
  code := gridToClifford
  correct x := (gridToClifford_correct x).trans (gateFamilyFreeSwaps_on_outputs Γ supports x).symm

end CliffordSynthesis
