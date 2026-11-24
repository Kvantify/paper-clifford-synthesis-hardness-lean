/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingTraceCode
public import GridHardness.SatClauseBodyCatalogue
public import GridHardness.CorrectedSatIntervalNumberedAdjacency

/-!
# SAT Retained Drawing Code

SAT-fed coordinates and routes of the retained crossing bodies. Fresh
labels use the exact chronological trace position, while the emitted cells
may use the independently defined geometric crossing enumeration.
-/

@[expose] public section

namespace GridHardness.SatRetainedDrawingCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly CorrectedSatInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000
attribute [local irreducible] SatCrossingTraceCode.rankValue SatCrossingTraceCode.traceIndex
  PlanarSatCode.varCount SatClauseOrderCode.crossings

abbrev CellTy := Ty.pair SatTy SatCrossingCode.PairTy
abbrev VertexRecordTy := SatClauseBodyCode.VertexRecordTy
abbrev VerticesTy := SatClauseBodyCode.VerticesTy
abbrev RoutesTy := DirectedRouteLookupCode.RecordsTy
abbrev OutputTy := Ty.pair VerticesTy RoutesTy
abbrev Cell (x : SatTy.denote) := WireCrossingSchedule.Cell (SatClauseOrder.permutation (finiteFormula x))

def localVertices : List SatCrossingHorizontal.RetainedVertex :=
  (List.finRange 40).map NumberedAdjacency.retainedDecode

def localEdges : List SatRetainedDrawing.LocalEdge :=
  (List.finRange 66).filterMap (fun e => if h : SatCrossingHorizontal.RetainedEdge e
    then some ⟨e,h⟩ else none)

theorem mem_localVertices (v : SatCrossingHorizontal.RetainedVertex) : v∈localVertices := by
  exact List.mem_map.mpr ⟨Numbering.retainedIndex v,List.mem_finRange _,
    NumberedAdjacency.retainedDecode_index v⟩

theorem mem_localEdges (e : SatRetainedDrawing.LocalEdge) : e∈localEdges := by
  apply List.mem_filterMap.mpr
  exact ⟨e.val,List.mem_finRange _,by simp only [dite_eq_left e.property]⟩

theorem localVertices_length : localVertices.length=40 := by simp [localVertices]
theorem localEdges_length : localEdges.length=54 := by decide +kernel

def originX : Code CellTy SignedTy :=
  .comp (.pair (Code.add (Code.mul (.const .nat 512)
    (Code.add (.comp .snd .fst) (.const .nat 1))) (.const .nat 65)) (.const .nat 0)) normalize

def originY : Code CellTy SignedTy :=
  .comp (.pair (Code.mul (.const .nat 512)
    (Code.add (Code.add (Code.mul (.const .nat 3) (.comp .fst .listLen)) (.const .nat 2))
      (.comp (.pair .fst (.comp .snd .snd)) SatCrossingTraceCode.rankValue))) (.const .nat 10)) normalize

def frameCode : Code CellTy FrameTy :=
  .pair (.const .bool false) (.pair (.const .bool false)
    (.pair (.const .bool true) (.pair originX originY)))

def encodeCell {x : SatTy.denote} (c : Cell x) : Nat×Nat := (c.val.1.val,c.val.2.val)

theorem frameCode_eval (x : SatTy.denote) (c : Cell x) :
    frameCode.eval (x,encodeCell c)=encodeFrame
      (SatCrossingLattice.frame (SatClauseOrder.permutation (finiteFormula x)) c.val) := by
  have hx : originX.eval (x,encodeCell c)=encodeInt (512*PermutationWireLayout.low c.val.1+65) := by
    change normalize.eval (512*(c.val.1.val+1)+65,0)=_
    rw [normalize_eval]
    congr 1
  have hy : originY.eval (x,encodeCell c)=encodeInt
      (512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) c.val.2-10) := by
    change normalize.eval (512*(3*x.length+2+SatCrossingTraceCode.rankValue.eval (x,c.val.2.val)),10)=_
    rw [SatCrossingTraceCode.rankValue_eval,normalize_eval]
    congr 1
  change (false,false,true,originX.eval (x,encodeCell c),originY.eval (x,encodeCell c))=_
  rw [hx,hy]
  rfl

def labelCode (v : SatCrossingHorizontal.RetainedVertex) : Code CellTy .nat :=
  Code.add (Code.add
    (Code.add (Code.add (.const .nat 3) (Code.mul (.const .nat 2) (.comp .fst PlanarSatCode.varCount)))
      (Code.mul (.const .nat 36) (.comp .fst .listLen)))
    (Code.mul (.const .nat 40) SatCrossingTraceCode.traceIndex))
    (.const .nat (Numbering.retainedIndex v).val)

noncomputable def label (x : SatTy.denote) (c : Cell x) (v : SatCrossingHorizontal.RetainedVertex) : Nat :=
  SatClauseBodyCode.actualLabel x (PermutationWirePlacement.fresh (finiteFormula x)
    (SatClauseOrder.permutation (finiteFormula x)) c v)

theorem labelCode_eval (x : SatTy.denote) (c : Cell x) (v : SatCrossingHorizontal.RetainedVertex) :
    (labelCode v).eval (x,encodeCell c)=label x c v := by
  change 3+2*PlanarSatCode.varCount.eval x+36*x.length+
    40*SatCrossingTraceCode.traceIndex.eval (x,encodeCell c)+(Numbering.retainedIndex v).val=_
  rw [PlanarSatCode.varCount_eval]
  unfold encodeCell
  rw [SatCrossingTraceCode.traceIndex_eval]
  exact (PermutationWirePlacement.fresh_names (finiteFormula x)
    (SatClauseOrder.permutation (finiteFormula x)) c v).symm

def pointCode (v : SatCrossingHorizontal.RetainedVertex) : Code CellTy PointTy :=
  .comp (.pair frameCode (.const PointTy (encodePoint (XorLine.Lattice.point v.val)))) GridFrameCode.point

def routeCode (e : SatRetainedDrawing.LocalEdge) : Code CellTy CycleInputTy :=
  .comp (.pair frameCode (.const CycleInputTy ((XorLine.Lattice.edgeRoute e.val).map encodePoint)))
    (.listMapEnv GridFrameCode.point)

theorem pointCode_eval (x : SatTy.denote) (c : Cell x) (v : SatCrossingHorizontal.RetainedVertex) :
    (pointCode v).eval (x,encodeCell c)=encodePoint
      (SatRetainedDrawing.point (SatClauseOrder.permutation (finiteFormula x)) (c,v)) := by
  change GridFrameCode.point.eval (frameCode.eval (x,encodeCell c),encodePoint _)=_
  rw [frameCode_eval,GridFrameCode.point_eval,decode_encodeFrame,GridAssembly.Encoding.decode_encode]
  rfl

theorem routeCode_eval (x : SatTy.denote) (c : Cell x) (e : SatRetainedDrawing.LocalEdge) :
    (routeCode e).eval (x,encodeCell c)=
      (SatRetainedDrawing.route (SatClauseOrder.permutation (finiteFormula x)) (c,e)).map encodePoint := by
  change ((XorLine.Lattice.edgeRoute e.val).map encodePoint).map
    (fun q => GridFrameCode.point.eval (frameCode.eval (x,encodeCell c),q))=_
  rw [frameCode_eval,List.map_map]
  change (XorLine.Lattice.edgeRoute e.val).map _=
    ((XorLine.Lattice.edgeRoute e.val).map
      (SatCrossingLattice.frame (SatClauseOrder.permutation (finiteFormula x)) c.val).map).map encodePoint
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_def]
  rw [GridFrameCode.point_eval,decode_encodeFrame,GridAssembly.Encoding.decode_encode]

noncomputable def vertexRecord (x : SatTy.denote) (c : Cell x)
    (v : SatCrossingHorizontal.RetainedVertex) : VertexRecordTy.denote :=
  (label x c v,encodePoint (SatRetainedDrawing.point (SatClauseOrder.permutation (finiteFormula x)) (c,v)))

noncomputable def routeRecord (x : SatTy.denote) (c : Cell x)
    (e : SatRetainedDrawing.LocalEdge) : DirectedRouteLookupCode.RecordTy.denote :=
  ((label x c (SatRetainedDrawing.localEndpoints e).1,label x c (SatRetainedDrawing.localEndpoints e).2),
    (SatRetainedDrawing.route (SatClauseOrder.permutation (finiteFormula x)) (c,e)).map encodePoint)

def vertexAt (v : SatCrossingHorizontal.RetainedVertex) : Code CellTy VertexRecordTy :=
  .pair (labelCode v) (pointCode v)
def routeAt (e : SatRetainedDrawing.LocalEdge) : Code CellTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair (labelCode (SatRetainedDrawing.localEndpoints e).1)
    (labelCode (SatRetainedDrawing.localEndpoints e).2)) (routeCode e)

theorem vertexAt_eval (x : SatTy.denote) (c : Cell x) (v : SatCrossingHorizontal.RetainedVertex) :
    (vertexAt v).eval (x,encodeCell c)=vertexRecord x c v := by
  change ((labelCode v).eval (x,encodeCell c),(pointCode v).eval (x,encodeCell c))=_
  rw [labelCode_eval,pointCode_eval]
  rfl

theorem routeAt_eval (x : SatTy.denote) (c : Cell x) (e : SatRetainedDrawing.LocalEdge) :
    (routeAt e).eval (x,encodeCell c)=routeRecord x c e := by
  change (((labelCode (SatRetainedDrawing.localEndpoints e).1).eval (x,encodeCell c),
    (labelCode (SatRetainedDrawing.localEndpoints e).2).eval (x,encodeCell c)),
    (routeCode e).eval (x,encodeCell c))=_
  rw [labelCode_eval,labelCode_eval,routeCode_eval]
  rfl

def verticesAt : Code CellTy VerticesTy := PlanarSatCode.table localVertices vertexAt
def routesAt : Code CellTy RoutesTy := PlanarSatCode.table localEdges routeAt
attribute [local irreducible] verticesAt routesAt

def vertices : Code SatTy VerticesTy :=
  .comp (.pair .id SatClauseOrderCode.crossings) (.comp (.listMapEnv verticesAt) .listJoin)
def routes : Code SatTy RoutesTy :=
  .comp (.pair .id SatClauseOrderCode.crossings) (.comp (.listMapEnv routesAt) .listJoin)
def code : Code SatTy OutputTy := .pair vertices routes

/-- This list keeps the geometric enumeration order while carrying its proof. -/
def cells (x : SatTy.denote) : List (Cell x) :=
  (SatClauseOrderCode.crossings.eval x).attach.map (SatClauseOrderCode.cellListEquiv x)

theorem cells_encoded (x : SatTy.denote) : (cells x).map encodeCell=SatClauseOrderCode.crossings.eval x := by
  simp only [cells,List.map_map]
  change ((SatClauseOrderCode.crossings.eval x).attach.map Subtype.val)=_
  simpa only [id_eq,List.map_id] using
    (List.attach_map_val (l:=SatClauseOrderCode.crossings.eval x) (f:=id))

theorem cells_complete (x : SatTy.denote) (c : Cell x) : c∈cells x := by
  apply List.mem_map.mpr
  exact ⟨(SatClauseOrderCode.cellListEquiv x).symm c,List.mem_attach _ _,
    (SatClauseOrderCode.cellListEquiv x).apply_symm_apply c⟩

theorem vertices_eval (x : SatTy.denote) : vertices.eval x=
    (cells x).flatMap (fun c => localVertices.map (vertexRecord x c)) := by
  change ((SatClauseOrderCode.crossings.eval x).map (fun c => verticesAt.eval (x,c))).flatten=_
  rw [← cells_encoded,List.map_map,← List.flatMap_def]
  apply List.flatMap_congr
  intro c _
  simp only [Function.comp_def]
  rw [verticesAt,PlanarSatCode.table_eval]
  exact List.map_congr_left (fun v _ => vertexAt_eval x c v)

theorem routes_eval (x : SatTy.denote) : routes.eval x=
    (cells x).flatMap (fun c => localEdges.map (routeRecord x c)) := by
  change ((SatClauseOrderCode.crossings.eval x).map (fun c => routesAt.eval (x,c))).flatten=_
  rw [← cells_encoded,List.map_map,← List.flatMap_def]
  apply List.flatMap_congr
  intro c _
  simp only [Function.comp_def]
  rw [routesAt,PlanarSatCode.table_eval]
  exact List.map_congr_left (fun e _ => routeAt_eval x c e)

theorem emitted_arc (x : SatTy.denote) (c : Cell x) (e : SatRetainedDrawing.LocalEdge) :
    (SatClauseOrder.graph (finiteFormula x)).adj
      (SatRetainedDrawing.source (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) (c,e))
      (SatRetainedDrawing.target (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) (c,e)) :=
  SatRetainedDrawing.edge_is_arc (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) (c,e)

end GridHardness.SatRetainedDrawingCode
