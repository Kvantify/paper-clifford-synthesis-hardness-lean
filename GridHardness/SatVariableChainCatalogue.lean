/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableChainRecordsCode

/-!
# SAT Variable Chain Catalogue

The executable variable-chain family in the final graph's route catalogue.
-/

@[expose] public section

namespace GridHardness.SatVariableChainRecordsCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatClauseBodyCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def catalogueIndex (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    SatWireDrawingGeometry.Edge x :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (.inl e))))))))

theorem record_actual (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    record x e=
      ((actualLabel x (SatWireDrawingGeometry.source x (catalogueIndex x e)),
        actualLabel x (SatWireDrawingGeometry.target x (catalogueIndex x e))),
        (SatWireDrawingGeometry.route x (catalogueIndex x e)).map encodePoint) := by
  change ((_,_),(SatVariableChainDrawing.route e).map encodePoint)=
    ((actualLabel x (SatVariableChainDrawing.vertex (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) (SatVariableChainDrawing.endpoints e).1),
      actualLabel x (SatVariableChainDrawing.vertex (finiteFormula x)
        (SatClauseOrder.permutation (finiteFormula x)) (SatVariableChainDrawing.endpoints e).2)),_)
  simp only [actualLabel,SatVariableChainDrawing.vertex,CorrectedSatInterval.PermutationGraph.original_names]
  rfl

theorem emitted_arc (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    (SatClauseOrder.graph (finiteFormula x)).adj
      (SatWireDrawingGeometry.source x (catalogueIndex x e))
      (SatWireDrawingGeometry.target x (catalogueIndex x e)) :=
  SatVariableChainDrawing.edge_is_arc (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) e

end GridHardness.SatVariableChainRecordsCode
