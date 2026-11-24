/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingWireVertices
public import GridHardness.CorrectedSatIntervalGlobalNumbering

/-!
# Corrected SAT Interval Wire Placement

Identify the simultaneous wire-vertex placement with actual vertices of
the final sweep graph. This covers all occurrence XORs and all retained
crossing vertices; variable, clause and sentinel vertices remain separate.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.WirePlacement
open CliffordComplexity PlanarSatAssembly GlobalNumbering
set_option autoImplicit false

abbrev WireVertex (x : SatTy.denote) :=
  SatCrossingWireVertices.Vertex (SatWireLayout.permutation (finiteFormula x))

def names (x : SatTy.denote) : WireVertex x →
    PlanarSatAssembly.Vertex ((vsOf x).length+1) x.length ⊕
      ({c : Nat × Nat // c∈SatCrossingCode.crossings.eval x} ×
        SatCrossingHorizontal.RetainedVertex)
  | .inl (j,v) => .inl (xor ((SatWireLayout.variableRank (finiteFormula x)).symm j) v)
  | .inr (c,v) => .inr ((SatCrossingCode.cellListEquiv x).symm c,v)

theorem names_injective (x : SatTy.denote) : Function.Injective (names x) := by
  intro u v he
  cases u with
  | inl jv =>
    cases v with
    | inl kw =>
      have h := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inl.inj he)))
      have hj := (SatWireLayout.variableRank (finiteFormula x)).symm.injective (congrArg Prod.fst h)
      have hv := (Prod.mk.inj h).2
      exact congrArg Sum.inl (Prod.ext hj hv)
    | inr cv => cases he
  | inr cv =>
    cases v with
    | inl jv => cases he
    | inr dw =>
      have h := Sum.inr.inj he
      have hv := (Prod.mk.inj h).2
      exact congrArg Sum.inr (Prod.ext ((SatCrossingCode.cellListEquiv x).symm.injective
        (congrArg Prod.fst h)) hv)

noncomputable def vertex (x : SatTy.denote) (v : WireVertex x) : (actualGraph x).Vertex :=
  (actualDecomposition x).symm (names x v)

theorem vertex_injective (x : SatTy.denote) : Function.Injective (vertex x) :=
  (actualDecomposition x).symm.injective.comp (names_injective x)

theorem vertex_original (x : SatTy.denote) (j : Fin (3 *x.length)) (v : Fin 8) :
    vertex x (.inl (j,v)) = formulaLift (finiteFormula x)
      (xor ((SatWireLayout.variableRank (finiteFormula x)).symm j) v) := by
  apply (actualDecomposition x).injective
  rw [vertex,Equiv.apply_symm_apply,actualDecomposition_old]
  rfl

theorem vertex_fresh (x : SatTy.denote)
    (c : WireCrossingSchedule.Cell (SatWireLayout.permutation (finiteFormula x)))
    (v : SatCrossingHorizontal.RetainedVertex) :
    vertex x (.inr (c,v)) = actualFresh x ((SatCrossingCode.cellListEquiv x).symm c) v := by
  apply (actualDecomposition x).injective
  rw [vertex,Equiv.apply_symm_apply,actualDecomposition_fresh]
  rfl

def point (x : SatTy.denote) (v : WireVertex x) : Int × Int :=
  SatCrossingWireVertices.point (SatWireLayout.permutation (finiteFormula x)) v

theorem point_injective (x : SatTy.denote) : Function.Injective (point x) :=
  SatCrossingWireVertices.point_injective _

/-- Equal positions are exactly equal actual graph vertices on this complete
wire family. This simultaneously excludes collisions across different wires
and across different crossing remnants. -/
theorem same_point_iff_same_vertex (x : SatTy.denote) (u v : WireVertex x) :
    point x u=point x v ↔ vertex x u=vertex x v := by
  constructor
  · intro h
    exact congrArg (vertex x) (point_injective x h)
  · intro h
    exact congrArg (point x) (vertex_injective x h)

theorem point_bounds (x : SatTy.denote) (v : WireVertex x) :
    0≤(point x v).1 ∧ (point x v).1≤512*(3*x.length+1)+65 ∧
      0≤(point x v).2 ∧ (point x v).2≤1024*(3*x.length)+522 :=
  SatCrossingWireVertices.point_bounds _ v

end GridHardness.CorrectedSatInterval.WirePlacement
