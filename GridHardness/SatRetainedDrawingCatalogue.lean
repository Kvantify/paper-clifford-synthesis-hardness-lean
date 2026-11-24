/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetainedDrawingCode

/-!
# SAT Retained Drawing Catalogue

Exact catalogue coverage by the syntax-driven retained-crossing compiler.
-/

@[expose] public section

namespace GridHardness.SatRetainedDrawingCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def catalogueIndex (x : SatTy.denote) (c : Cell x) (e : SatRetainedDrawing.LocalEdge) :
    SatWireDrawingGeometry.Edge x := .inl (.inl (.inl (.inl (.inl (.inr (c,e))))))

theorem routeRecord_actual (x : SatTy.denote) (c : Cell x) (e : SatRetainedDrawing.LocalEdge) :
    routeRecord x c e=
      ((SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.source x (catalogueIndex x c e)),
        SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.target x (catalogueIndex x c e))),
        (SatWireDrawingGeometry.route x (catalogueIndex x c e)).map encodePoint) := rfl

theorem vertexRecord_actual (x : SatTy.denote) (c : Cell x) (v : SatCrossingHorizontal.RetainedVertex) :
    vertexRecord x c v=
      (SatClauseBodyCode.actualLabel x (SatRetainedDrawing.vertex (finiteFormula x)
        (SatClauseOrder.permutation (finiteFormula x)) (c,v)),
        encodePoint (SatGlobalVertexPlacement.actualPoint (finiteFormula x)
          (SatRetainedDrawing.vertex (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) (c,v)))) := by
  rw [SatRetainedDrawing.actualPoint_vertex]; rfl

theorem mem_routes (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈routes.eval x ↔ ∃ c : Cell x,∃ e : SatRetainedDrawing.LocalEdge,r=routeRecord x c e := by
  rw [routes_eval,List.mem_flatMap]
  constructor
  · rintro ⟨c,_,hr⟩
    obtain ⟨e,_,he⟩ := List.mem_map.mp hr
    exact ⟨c,e,he.symm⟩
  · rintro ⟨c,e,rfl⟩
    exact ⟨c,cells_complete x c,List.mem_map.mpr ⟨e,mem_localEdges e,rfl⟩⟩

theorem mem_vertices (x : SatTy.denote) (r : VertexRecordTy.denote) :
    r∈vertices.eval x ↔ ∃ c : Cell x,∃ v : SatCrossingHorizontal.RetainedVertex,r=vertexRecord x c v := by
  rw [vertices_eval,List.mem_flatMap]
  constructor
  · rintro ⟨c,_,hr⟩
    obtain ⟨v,_,he⟩ := List.mem_map.mp hr
    exact ⟨c,v,he.symm⟩
  · rintro ⟨c,v,rfl⟩
    exact ⟨c,cells_complete x c,List.mem_map.mpr ⟨v,mem_localVertices v,rfl⟩⟩

end GridHardness.SatRetainedDrawingCode
