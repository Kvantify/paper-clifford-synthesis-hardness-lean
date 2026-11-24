/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableBodyCode

/-!
# SAT Variable Body Catalogue

Identification of variable-body records with the full route catalogue.
-/

@[expose] public section

namespace GridHardness.SatVariableBodyCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatClauseBodyCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem mem_code (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈code.eval x ↔ ∃ e,r=record x e := by
  rw [code_eval,List.mem_map]
  constructor
  · rintro ⟨e,_,h⟩; exact ⟨e,h.symm⟩
  · rintro ⟨e,rfl⟩; exact ⟨e,mem_edges x e,rfl⟩

def catalogueIndex (x : SatTy.denote) (e : SatVariableDrawing.Edge ((vsOf x).length +1)) :
    SatWireDrawingGeometry.Edge x :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl e))))))))

theorem record_actual (x : SatTy.denote) (e : SatVariableDrawing.Edge ((vsOf x).length +1)) :
    record x e=
      ((actualLabel x (SatWireDrawingGeometry.source x (catalogueIndex x e)),
        actualLabel x (SatWireDrawingGeometry.target x (catalogueIndex x e))),
        (SatWireDrawingGeometry.route x (catalogueIndex x e)).map encodePoint) := by
  change ((_,_),(SatVariableDrawing.route (finiteFormula x) e).map encodePoint)=
    ((actualLabel x (SatVariableDrawing.vertex (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) (SatVariableDrawing.endpoints e).1),
      actualLabel x (SatVariableDrawing.vertex (finiteFormula x)
        (SatClauseOrder.permutation (finiteFormula x)) (SatVariableDrawing.endpoints e).2)),_)
  simp only [actualLabel,SatVariableDrawing.vertex,CorrectedSatInterval.PermutationGraph.original_names,
    PlanarSatCode.numbering_var,PlanarSatCode.varNum_eval]
  rfl

theorem emitted_arc (x : SatTy.denote) (e : SatVariableDrawing.Edge ((vsOf x).length +1)) :
    (SatClauseOrder.graph (finiteFormula x)).adj
      (SatWireDrawingGeometry.source x (catalogueIndex x e))
      (SatWireDrawingGeometry.target x (catalogueIndex x e)) :=
  SatBodyDrawing.edge_is_arc (finiteFormula x) (.inl e)

end GridHardness.SatVariableBodyCode
