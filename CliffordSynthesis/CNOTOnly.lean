/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Certified

/-!
# CNOT Only

Equivalence between the CNOT-only language and phase-free synthesis on the grid
reduction outputs, and the resulting certified reduction.
-/

@[expose] public section

open GridProblems GridProblems.GridCode

namespace CliffordSynthesis
open CliffordComplexity
open MatrixCompiler GridProblems.GridCode GridCompiler

theorem cnotOnly_implies_accepts {out : OutputTy.denote} (h : CNOTOnly out) : Accepts out := by
  obtain ⟨cs, hl, ht⟩ := h
  exact ⟨RowHistory.asCircuit cs, by rwa [RowHistory.circuit_cost], ht⟩

/-- On the reduction's outputs, free one-qubit Cliffords do not improve the
answer relative to CNOT-only synthesis. This is specific to this construction. -/
theorem cnotOnly_on_outputs (x : InputTy.denote) :
    CNOTOnly (gridToClifford.eval x) ↔ Accepts (gridToClifford.eval x) := by
  refine ⟨cnotOnly_implies_accepts, ?_⟩
  intro h
  obtain ⟨m, p, last, rfl, hp, w, hw⟩ := (gridToClifford_correct x).mpr h
  have hv := (validCode_eval p last).mpr hp
  have hwindow := BoundedGrid.hamiltonian_inWindow (decoded ∘ p) last w hw
  have ht := (windowTest_eval p last).mpr hwindow
  change CNOTOnly (if validCode.eval (input p last) then CliffordSynthesis.GridCompiler.reduce.eval (input p last) else noOutput)
  rw [ite_eq_left hv]
  change CNOTOnly (if windowTest.eval (input p last) then compile.eval (template.eval (input p last)) else noOutput)
  rw [ite_eq_left ht, template_eval, compile_encode (BoundedGrid.vertex (decoded ∘ p) last)
    (ReplicatedTarget.repeated (BoundedGrid.vertex (decoded ∘ p)) (EncodedTarget.copies m))]
  unfold CNOTOnly
  rw [decode_encode _ _ (fun _ _ => rfl) (fun _ _ => rfl)]
  have hs : Circuit.SynthesizesWithin
      (EncodedTarget.instanceTableau (BoundedGrid.vertex (decoded ∘ p)) last)
      (EncodedTarget.recorderCount m + m) := by
    apply (CliffordSynthesis.Reduction.synthesis_iff_hamiltonian _
      (BoundedGrid.vertex_injective _ hwindow hp) (BoundedGrid.vertex_zero _) last).mpr
    rw [BoundedGrid.graph_eq _ hwindow]
    exact ⟨w, hw⟩
  obtain ⟨cs, hl, hx⟩ := EncodedTarget.synthesis_to_row_circuit _
    (BoundedGrid.vertex_injective _ hwindow hp) (BoundedGrid.vertex_zero _) last hs
  exact ⟨cs, hl.le, ClassicalLift.same_target _ cs _ _ hx⟩

/-- The same certified program also reduces grid Hamiltonian path to CNOT-only
synthesis; this provides both gate-library variants of the core reduction. -/
def certifiedGridToCNOTOnly : CertifiedReduction GRID_HAMILTONIAN_PATH CNOTOnly where
  code := gridToClifford
  correct x := (gridToClifford_correct x).trans (cnotOnly_on_outputs x).symm

end CliffordSynthesis
