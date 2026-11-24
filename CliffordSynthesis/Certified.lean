/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridProblems.Source
public import CliffordSynthesis.Validity

/-!
# Certified

A polynomial-time reduction from specified-endpoint Hamiltonian path
in an induced integer grid to CNOT-count minimization.
-/

@[expose] public section

open GridProblems GridProblems.GridCode

namespace CliffordSynthesis
open CliffordComplexity
open GridProblems.GridCode GridCompiler MatrixCompiler

/-- The total program rejects empty inputs, duplicate grid vertices, and
out-of-range endpoints before running the bounded-window reduction. -/
def gridToClifford : Code InputTy OutputTy :=
  .branch validCode CliffordSynthesis.GridCompiler.reduce (.const OutputTy noOutput)

theorem gridToClifford_correct (x : InputTy.denote) :
    GRID_HAMILTONIAN_PATH x ↔ Accepts (gridToClifford.eval x) := by
  by_cases hv : validCode.eval x = true
  · obtain ⟨m, p, last, rfl, hp⟩ := (validCode_correct x).mp hv
    change GRID_HAMILTONIAN_PATH (input p last) ↔
      Accepts (if validCode.eval (input p last) then CliffordSynthesis.GridCompiler.reduce.eval (input p last) else noOutput)
    rw [ite_eq_left hv, reduce_correct p hp last, source_input]
    exact and_iff_right hp
  · change GRID_HAMILTONIAN_PATH x ↔ Accepts (if validCode.eval x then CliffordSynthesis.GridCompiler.reduce.eval x else noOutput)
    rw [ite_eq_right hv]
    exact iff_of_false (fun h => hv ((validCode_correct x).mpr (source_valid h))) noOutput_rejects

/-- The many-one reduction to CNOT-count minimization. -/
def certifiedGridToClifford : CertifiedReduction GRID_HAMILTONIAN_PATH Accepts where
  code := gridToClifford
  correct := gridToClifford_correct

/-- The certified concrete source includes every injective signed integer grid
with specified endpoints, not merely a bounded or unary-coordinate subclass. -/
theorem signed_grid_correct {m : Nat} (point : Fin (m + 1) → Int × Int)
    (hp : Function.Injective point) (last : Fin (m + 1)) :
    Accepts (gridToClifford.eval (input (encodePoint ∘ point) last)) ↔
      ∃ w : (IntegerGrid.graph point).Walk 0 last, w.IsHamiltonian := by
  rw [← gridToClifford_correct, source_input]
  have hd : decoded ∘ (encodePoint ∘ point) = point := by
    funext i
    simp [decoded, encodePoint, Function.comp_def]
  rw [hd]
  exact and_iff_right hp

end CliffordSynthesis
