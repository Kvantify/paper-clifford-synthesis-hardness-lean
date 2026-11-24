/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetirementGeometryCode

/-!
# SAT Retired Drawing Code

Polynomial compilation of the eight original vertices and six side
edges of every retired XOR. Labels are the final graph's preserved original
labels, obtained by indexing the variable-order occurrence list.
-/

@[expose] public section

namespace GridHardness.SatRetiredDrawingCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly CorrectedSatInterval SatRetirementGeometryCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000

abbrev RowTy := SatRetirementGeometryCode.RowTy
abbrev VertexRecordTy := SatClauseBodyCode.VertexRecordTy
abbrev VerticesTy := SatClauseBodyCode.VerticesTy
abbrev RoutesTy := DirectedRouteLookupCode.RecordsTy
abbrev OutputTy := Ty.pair VerticesTy RoutesTy

def occurrenceCode : Code RowTy PlanarSatCode.OccTy :=
  .comp (.pair (.comp .fst SatClauseOrderCode.occurrences) .snd)
    (.pair (lookupNat PlanarSatCode.OccTy .fst) (lookupNat PlanarSatCode.OccTy .snd))

theorem occurrenceCode_eval (x : SatTy.denote) (j : Fin (3 *x.length)) :
    occurrenceCode.eval (x,j.val)=
      PlanarSatCode.occVal ((SatWireLayout.variableRank (finiteFormula x)).symm j) := by
  have hl : (SatClauseOrderCode.occurrences.eval x).length=3*x.length := by
    rw [SatClauseOrderCode.occurrences_eval,List.length_map,SatWireLayout.variableOrder_length]
  change ((lookupNat PlanarSatCode.OccTy .fst).eval (SatClauseOrderCode.occurrences.eval x,j.val),
    (lookupNat PlanarSatCode.OccTy .snd).eval (SatClauseOrderCode.occurrences.eval x,j.val))=_
  rw [lookupNat_eval _ _ _ _ (by rw [hl]; exact j.isLt),
    lookupNat_eval _ _ _ _ (by rw [hl]; exact j.isLt)]
  simp only [Code.eval,SatClauseOrderCode.occurrences_eval,List.getElem_map]
  rfl

def labelCode (v : Fin 8) : Code RowTy .nat :=
  .comp (.pair .fst occurrenceCode) (PlanarSatCode.xorNum v.val)

noncomputable def label (x : SatTy.denote) (j : Fin (3 *x.length)) (v : Fin 8) : Nat :=
  SatClauseBodyCode.actualLabel x (SatRetiredSideDrawing.vertex (finiteFormula x) (perm x) (j,v))

theorem labelCode_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (v : Fin 8) :
    (labelCode v).eval (x,j.val)=label x j v := by
  change (PlanarSatCode.xorNum v.val).eval (x,occurrenceCode.eval (x,j.val))=_
  rw [occurrenceCode_eval]
  change _=(PermutationGraph.number _ _ (PermutationWirePlacement.vertex _ _ (.inl (j,v)))).val
  rw [PermutationWirePlacement.vertex_original,PermutationGraph.original_names,PlanarSatCode.xorNum_eval]
  rfl

noncomputable def vertexRecord (x : SatTy.denote) (j : Fin (3 *x.length)) (v : Fin 8) : VertexRecordTy.denote :=
  (label x j v,encodePoint (SatRetiredSideDrawing.point (perm x) (j,v)))
noncomputable def routeRecord (x : SatTy.denote) (j : Fin (3 *x.length)) (e : Fin 6) :
    DirectedRouteLookupCode.RecordTy.denote :=
  ((label x j (SatRetiredSideDrawing.localEndpoints e).1,
    label x j (SatRetiredSideDrawing.localEndpoints e).2),
    (SatRetiredSideDrawing.route (perm x) (j,e)).map encodePoint)

def vertexAt (v : Fin 8) : Code RowTy VertexRecordTy := .pair (labelCode v) (pointCode v)
def routeAt (e : Fin 6) : Code RowTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair (labelCode (SatRetiredSideDrawing.localEndpoints e).1)
    (labelCode (SatRetiredSideDrawing.localEndpoints e).2)) (sideCode e)

theorem vertexAt_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (v : Fin 8) :
    (vertexAt v).eval (x,j.val)=vertexRecord x j v := by
  change ((labelCode v).eval (x,j.val),(pointCode v).eval (x,j.val))=_
  rw [labelCode_eval,pointCode_eval]; rfl

theorem routeAt_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (e : Fin 6) :
    (routeAt e).eval (x,j.val)=routeRecord x j e := by
  change (((labelCode _).eval (x,j.val),(labelCode _).eval (x,j.val)),(sideCode e).eval (x,j.val))=_
  rw [labelCode_eval,labelCode_eval,sideCode_eval]; rfl

def verticesAt : Code RowTy VerticesTy := PlanarSatCode.table (List.finRange 8) vertexAt
def routesAt : Code RowTy RoutesTy := PlanarSatCode.table (List.finRange 6) routeAt

def rows : Code SatTy (.list .nat) := .comp SatClauseOrderCode.permutation Code.indices

theorem rows_eval (x : SatTy.denote) : rows.eval x=(List.finRange (3*x.length)).map Fin.val := by
  change Code.indices.eval (SatClauseOrderCode.permutation.eval x)=_
  rw [indices_eval,SatClauseOrderCode.permutation_length]
  simp

def vertices : Code SatTy VerticesTy :=
  .comp (.pair .id rows) (.comp (.listMapEnv verticesAt) .listJoin)
def routes : Code SatTy RoutesTy :=
  .comp (.pair .id rows) (.comp (.listMapEnv routesAt) .listJoin)
def code : Code SatTy OutputTy := .pair vertices routes

theorem vertices_eval (x : SatTy.denote) : vertices.eval x=
    (List.finRange (3*x.length)).flatMap (fun j => (List.finRange 8).map (vertexRecord x j)) := by
  change ((rows.eval x).map (fun j => verticesAt.eval (x,j))).flatten=_
  rw [rows_eval,List.map_map,← List.flatMap_def]
  apply List.flatMap_congr
  intro j _
  simp only [Function.comp_def]
  rw [verticesAt,PlanarSatCode.table_eval]
  exact List.map_congr_left (fun v _ => vertexAt_eval x j v)

theorem routes_eval (x : SatTy.denote) : routes.eval x=
    (List.finRange (3*x.length)).flatMap (fun j => (List.finRange 6).map (routeRecord x j)) := by
  change ((rows.eval x).map (fun j => routesAt.eval (x,j))).flatten=_
  rw [rows_eval,List.map_map,← List.flatMap_def]
  apply List.flatMap_congr
  intro j _
  simp only [Function.comp_def]
  rw [routesAt,PlanarSatCode.table_eval]
  exact List.map_congr_left (fun e _ => routeAt_eval x j e)

theorem mem_vertices (x : SatTy.denote) (r : VertexRecordTy.denote) :
    r∈vertices.eval x ↔ ∃j v,r=vertexRecord x j v := by
  rw [vertices_eval]
  simp only [List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
  constructor
  · rintro ⟨j,v,h⟩; exact ⟨j,v,h.symm⟩
  · rintro ⟨j,v,h⟩; exact ⟨j,v,h.symm⟩

theorem mem_routes (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈routes.eval x ↔ ∃j e,r=routeRecord x j e := by
  rw [routes_eval]
  simp only [List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
  constructor
  · rintro ⟨j,e,h⟩; exact ⟨j,e,h.symm⟩
  · rintro ⟨j,e,h⟩; exact ⟨j,e,h.symm⟩

theorem vertices_length (x : SatTy.denote) : (vertices.eval x).length=24*x.length := by
  rw [vertices_eval,List.length_flatMap]; simp; omega

theorem routes_length (x : SatTy.denote) : (routes.eval x).length=18*x.length := by
  rw [routes_eval,List.length_flatMap]; simp; omega

end GridHardness.SatRetiredDrawingCode
