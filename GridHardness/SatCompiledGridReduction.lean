/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatDirectedRecordsCode
public import GridHardness.GridAssemblyCode
public import GridHardness.SatCompleteGridCorrectness
public import GridHardness.PositiveSat

/-!
# SAT Compiled Grid Reduction

Reduce positive one-in-three SAT to Hamiltonian path in a grid graph.
The polynomial-time program constructs the drawing and emits the encoded
grid instance directly from the formula.

## References

* [ItaiPapadimitriouSzwarcfiter1982]
-/

@[expose] public section

namespace GridHardness.SatCompiledGridReduction
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode
open GridPointCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SatDirectedRecordsCode.rectangles

/-- Reject malformed positive syntax before generating any geometric records. -/
def positiveCode : Code SatTy GridPointCode.InputTy :=
  .branch PlanarSatCode.syntaxGuard SatDirectedRecordsCode.rectangles
    (.const GridPointCode.InputTy [])

private theorem empty_not_cycle : ¬RECTANGLE_GRID_HAMILTONIAN_CYCLE [] := by
  rintro ⟨v,_,_⟩
  exact (Finset.eq_empty_iff_forall_notMem.mp GridAssembly.Rectangles.points_nil) v.val v.property

theorem positive_correct (x : SatTy.denote) :
    Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔ RECTANGLE_GRID_HAMILTONIAN_CYCLE (positiveCode.eval x) := by
  by_cases h : PlanarSatCode.syntaxGuard.eval x=true
  · obtain ⟨hw,hp⟩ := (PlanarSatCode.syntaxGuard_eval x).mp h
    rw [positiveCode,branch_eval_true _ _ h]
    unfold RECTANGLE_GRID_HAMILTONIAN_CYCLE
    rw [SatDirectedRecordsCode.rectangles_points x hw]
    exact SatCompleteGridCorrectness.induced_cycle_correct x hw hp
  · have hf := Bool.eq_false_iff.mpr h
    rw [positiveCode,branch_eval_false _ _ hf]
    change Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔ RECTANGLE_GRID_HAMILTONIAN_CYCLE []
    apply iff_of_false ?_ empty_not_cycle
    intro hx
    obtain ⟨hp,hw,_⟩ := (Concrete.monotoneOneInThree3Sat_iff x).mp hx
    exact h ((PlanarSatCode.syntaxGuard_eval x).mpr ⟨hw,hp⟩)

def positiveRectangles : CertifiedReduction Concrete.MONOTONE_ONE_IN_THREE_SAT3
    RECTANGLE_GRID_HAMILTONIAN_CYCLE := ⟨positiveCode,positive_correct⟩

def positivePath : CertifiedReduction Concrete.MONOTONE_ONE_IN_THREE_SAT3 GRID_HAMILTONIAN_PATH :=
  positiveRectangles.comp GridPointCode.certifiedToGridPath

end GridHardness.SatCompiledGridReduction
