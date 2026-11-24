/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBodyVertexCode
public import GridHardness.SatRetiredDrawingCatalogue
public import GridHardness.SatRetainedDrawingCatalogue

/-!
# SAT Vertex Catalogue Code

A complete SAT-fed list of the final directed graph's numbered vertex
coordinates. Enumeration covers the explicit body/wire decomposition, so it
needs neither a generic Fintype enumeration nor a semantic coordinate oracle.
-/

@[expose] public section

namespace GridHardness.SatVertexCatalogueCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatClauseBodyCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1200000

abbrev Vertex (x : SatTy.denote) := (SatClauseOrder.graph (finiteFormula x)).Vertex
noncomputable def record (x : SatTy.denote) (v : Vertex x) : VertexRecordTy.denote :=
  (actualLabel x v,encodePoint (SatGlobalVertexPlacement.actualPoint (finiteFormula x) v))

def code : Code SatTy VerticesTy :=
  Code.append (Code.append SatBodyVertexCode.code SatClauseBodyCode.vertices)
    (Code.append SatRetiredDrawingCode.vertices SatRetainedDrawingCode.vertices)

theorem code_eval (x : SatTy.denote) : code.eval x=
    (SatBodyVertexCode.sentinels.eval x++SatBodyVertexCode.variableRecords.eval x)++
      SatClauseBodyCode.vertices.eval x++
      (SatRetiredDrawingCode.vertices.eval x++SatRetainedDrawingCode.vertices.eval x) := by
  simp only [code,append_eval,SatBodyVertexCode.code]

theorem sound (x : SatTy.denote) (r : VertexRecordTy.denote) (hr : r ∈code.eval x) :
    ∃ v : Vertex x,r=record x v := by
  rw [code_eval] at hr
  simp only [List.mem_append] at hr
  rcases hr with ((hr | hr) | hr) | (hr | hr)
  · rw [SatBodyVertexCode.sentinels_eval] at hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact ⟨_,SatBodyVertexCode.sentinel_actual x i⟩
  · rw [SatBodyVertexCode.variables_eval] at hr
    obtain ⟨v,_,hr⟩ := List.mem_flatMap.mp hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_,SatBodyVertexCode.variableRecord_actual x v false⟩
    · exact ⟨_,SatBodyVertexCode.variableRecord_actual x v true⟩
  · obtain ⟨c,v,rfl⟩ := (SatClauseBodyCode.mem_vertices x r).mp hr
    exact ⟨_,SatClauseBodyCode.vertexRecord_actual x c v⟩
  · obtain ⟨j,v,rfl⟩ := (SatRetiredDrawingCode.mem_vertices x r).mp hr
    exact ⟨_,SatRetiredDrawingCode.vertexRecord_actual x j v⟩
  · obtain ⟨c,v,rfl⟩ := (SatRetainedDrawingCode.mem_vertices x r).mp hr
    exact ⟨_,SatRetainedDrawingCode.vertexRecord_actual x c v⟩

theorem complete (x : SatTy.denote) (v : Vertex x) : record x v∈code.eval x := by
  obtain ⟨z,rfl⟩ := (SatGlobalVertexPlacement.equiv (finiteFormula x)).surjective v
  rw [code_eval]
  simp only [List.mem_append]
  rcases z with (i | ⟨w,b⟩ | ⟨c,w⟩) | (⟨j,w⟩ | ⟨c,w⟩)
  · left; left; left
    rw [SatBodyVertexCode.sentinels_eval]
    apply List.mem_map.mpr
    refine ⟨i,List.mem_finRange _,?_⟩
    rw [SatGlobalVertexPlacement.equiv_body]
    exact SatBodyVertexCode.sentinel_actual x i
  · left; left; right
    rw [SatBodyVertexCode.variables_eval]
    apply List.mem_flatMap.mpr
    refine ⟨w,List.mem_finRange _,?_⟩
    rw [SatGlobalVertexPlacement.equiv_body]
    have he := SatBodyVertexCode.variableRecord_actual x w b
    change SatBodyVertexCode.variableRecord x w b=record x _ at he
    change record x (SatVariableDrawing.vertex (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) (w,b))∈_
    rw [← he]
    cases b <;> simp
  · left; right
    apply (SatClauseBodyCode.mem_vertices x _).mpr
    refine ⟨c,w,?_⟩
    rw [SatGlobalVertexPlacement.equiv_body]
    exact (SatClauseBodyCode.vertexRecord_actual x c w).symm
  · right; left
    apply (SatRetiredDrawingCode.mem_vertices x _).mpr
    refine ⟨j,w,?_⟩
    rw [SatGlobalVertexPlacement.equiv_wire]
    exact (SatRetiredDrawingCode.vertexRecord_actual x j w).symm
  · right; right
    apply (SatRetainedDrawingCode.mem_vertices x _).mpr
    refine ⟨c,w,?_⟩
    rw [SatGlobalVertexPlacement.equiv_wire,CorrectedSatInterval.PermutationWirePlacement.vertex_fresh]
    exact (SatRetainedDrawingCode.vertexRecord_actual x c w).symm

theorem mem_code (x : SatTy.denote) (r : VertexRecordTy.denote) :
    r∈code.eval x ↔ ∃v : Vertex x,r=record x v :=
  ⟨sound x r,by rintro ⟨v,rfl⟩; exact complete x v⟩

end GridHardness.SatVertexCatalogueCode
