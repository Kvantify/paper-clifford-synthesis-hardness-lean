/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatResidualBoundaryCode
public import GridHardness.SatResidualPathCode
public import GridHardness.SatRetainedDrawingCode

/-!
# SAT Residual Drawing Code

Full SAT-fed records for all residual lanes: an unsplit path in every
empty column, and the upper and lower tails at every nonempty column.
-/

@[expose] public section

namespace GridHardness.SatResidualDrawingCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly CorrectedSatInterval SatCrossingRetirement SatRetirementGeometryCode
open SatResidualBoundaryCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
attribute [local irreducible] SatRetiredDrawingCode.labelCode SatRetainedDrawingCode.labelCode
  SatRetirementPathCode.route SatResidualPathCode.code SatClauseBoundaryCode.vertical
  emptyRows decodeCell

abbrev RowTy := SatRetiredDrawingCode.RowTy
abbrev CellTy := SatResidualPathCode.CellTy
abbrev Edge (x : SatTy.denote) := SatResidualDrawing.Edge (perm x)
abbrev RoutesTy := DirectedRouteLookupCode.RecordsTy

noncomputable def routeRecord (x : SatTy.denote) (e : Edge x) : DirectedRouteLookupCode.RecordTy.denote :=
  ((SatClauseBodyCode.actualLabel x (SatResidualDrawing.source (finiteFormula x) (perm x) e),
    SatClauseBodyCode.actualLabel x (SatResidualDrawing.target (finiteFormula x) (perm x) e)),
    (SatResidualDrawing.route (perm x) e).map encodePoint)

def emptyEdge {x : SatTy.denote} (i : Empty x) (r : Fin 4) : Edge x :=
  ⟨i.val,r,.unsplit i.property⟩

def boundaryEdge {x : SatTy.denote} (b : Bool) (c : Cell x b) (r : Fin 4) : Edge x :=
  match b,c with
  | true,c => ⟨c.val.1,r,.above c.val.2 c.property⟩
  | false,c => ⟨c.val.1,r,.below c.val.2 c.property⟩

def emptyRecordAt (r : Fin 4) : Code RowTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair (SatRetiredDrawingCode.labelCode (XorGadget.arc (XorLine.Marked.crossArc r)).1)
    (SatRetiredDrawingCode.labelCode (XorGadget.arc (XorLine.Marked.crossArc r)).2))
    (SatRetirementPathCode.route r)

theorem emptyRecordAt_eval (x : SatTy.denote) (i : Empty x) (r : Fin 4) :
    (emptyRecordAt r).eval (x,i.val.val)=routeRecord x (emptyEdge i r) := by
  change (((SatRetiredDrawingCode.labelCode _).eval (x,i.val.val),
    (SatRetiredDrawingCode.labelCode _).eval (x,i.val.val)),
    (SatRetirementPathCode.route r).eval (x,i.val.val))=_
  rw [SatRetiredDrawingCode.labelCode_eval,SatRetiredDrawingCode.labelCode_eval,
    SatRetirementPathCode.route_eval]
  rfl

def oldLabel (v : Fin 8) : Code CellTy .nat :=
  .comp SatResidualPathCode.firstRow (SatRetiredDrawingCode.labelCode v)

def sourceLabel (r : Fin 4) (b : Bool) : Code CellTy .nat :=
  if b then
    if r.val%2=0 then oldLabel (falseVertex r)
    else SatRetainedDrawingCode.labelCode (SatResidualDrawing.output r)
  else
    if r.val%2=0 then SatRetainedDrawingCode.labelCode (SatResidualDrawing.output r)
    else oldLabel (trueVertex r)

def targetLabel (r : Fin 4) (b : Bool) : Code CellTy .nat :=
  if b then
    if r.val%2=0 then SatRetainedDrawingCode.labelCode (SatResidualDrawing.input r)
    else oldLabel (falseVertex r)
  else
    if r.val%2=0 then oldLabel (trueVertex r)
    else SatRetainedDrawingCode.labelCode (SatResidualDrawing.input r)

def boundaryRecordAt (r : Fin 4) (b : Bool) : Code CellTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair (sourceLabel r b) (targetLabel r b)) (SatResidualPathCode.code r b)

theorem boundaryRecordAt_eval (x : SatTy.denote) (b : Bool) (c : Cell x b) (r : Fin 4) :
    (boundaryRecordAt r b).eval (x,(c.val.1.val,c.val.2.val))=routeRecord x (boundaryEdge b c r) := by
  have ho (v : Fin 8) : (oldLabel v).eval (x,(c.val.1.val,c.val.2.val))=
      SatRetiredDrawingCode.label x c.val.1 v :=
    SatRetiredDrawingCode.labelCode_eval x c.val.1 v
  have ha : SatCrossingRouting.Active (perm x) c.val.1 c.val.2 := by
    cases b <;> exact c.property.1
  let ac : SatRetainedDrawingCode.Cell x := ⟨c.val,ha⟩
  have hf (v : SatCrossingHorizontal.RetainedVertex) :
      (SatRetainedDrawingCode.labelCode v).eval (x,(c.val.1.val,c.val.2.val))=
        SatRetainedDrawingCode.label x ac v :=
    SatRetainedDrawingCode.labelCode_eval x ac v
  change (((sourceLabel r b).eval (x,(c.val.1.val,c.val.2.val)),
    (targetLabel r b).eval (x,(c.val.1.val,c.val.2.val))),
    (SatResidualPathCode.code r b).eval (x,(c.val.1.val,c.val.2.val)))=_
  rw [SatResidualPathCode.code_eval x c.val.1 c.val.2 ha r b]
  cases b <;> by_cases hr : r.val%2=0
  all_goals
    simp only [sourceLabel,targetLabel,hr,ite_true,ite_false,Bool.false_eq_true,ite_false,ite_true]
    rw [ho,hf]
    simp only [routeRecord,boundaryEdge,SatResidualDrawing.source,SatResidualDrawing.target,
      SatResidualDrawing.sourceWire,SatResidualDrawing.targetWire,hr,ite_true,ite_false,
      SatResidualDrawing.route,Residual.route,Residual.path,
      SatRetiredDrawingCode.label,SatRetiredSideDrawing.vertex,
      SatRetainedDrawingCode.label,ac,PermutationWirePlacement.vertex_fresh]

def emptyAt : Code RowTy RoutesTy := PlanarSatCode.table (List.finRange 4) emptyRecordAt

def boundaryAt (b : Bool) : Code CellTy RoutesTy :=
  .comp (.pair .fst decodeCell)
    (PlanarSatCode.table (List.finRange 4) (fun r => boundaryRecordAt r b))

theorem boundaryAt_eval (x : SatTy.denote) (b : Bool) (c : Cell x b) :
    (boundaryAt b).eval (x,encodeCell c)=
      (List.finRange 4).map (fun r => routeRecord x (boundaryEdge b c r)) := by
  change (PlanarSatCode.table (List.finRange 4) (fun r => boundaryRecordAt r b)).eval
    (x,decodeCell.eval (x,encodeCell c))=_
  rw [decodeCell_eval,PlanarSatCode.table_eval]
  exact List.map_congr_left (fun r _ => boundaryRecordAt_eval x b c r)

def emptyRoutes : Code SatTy RoutesTy :=
  .comp (.pair .id emptyRows) (.comp (.listMapEnv emptyAt) .listJoin)
def boundaryRoutes (b : Bool) : Code SatTy RoutesTy :=
  .comp (.pair .id (SatClauseBoundaryCode.vertical b))
    (.comp (.listMapEnv (boundaryAt b)) .listJoin)

attribute [local irreducible] emptyAt boundaryAt

theorem emptyRoutes_eval (x : SatTy.denote) : emptyRoutes.eval x=
    (empties x).flatMap (fun i => (List.finRange 4).map (fun r => routeRecord x (emptyEdge i r))) := by
  change ((emptyRows.eval x).map (fun i => emptyAt.eval (x,i))).flatten=_
  rw [← empties_encoded,List.map_map,← List.flatMap_def]
  apply List.flatMap_congr
  intro i _
  simp only [Function.comp_def]
  rw [emptyAt,PlanarSatCode.table_eval]
  exact List.map_congr_left (fun r _ => emptyRecordAt_eval x i r)

theorem boundaryRoutes_eval (x : SatTy.denote) (b : Bool) : (boundaryRoutes b).eval x=
    (cells x b).flatMap (fun c => (List.finRange 4).map (fun r => routeRecord x (boundaryEdge b c r))) := by
  change (((SatClauseBoundaryCode.vertical b).eval x).map (fun c => (boundaryAt b).eval (x,c))).flatten=_
  rw [← cells_encoded,List.map_map,← List.flatMap_def]
  exact List.flatMap_congr (fun c _ => boundaryAt_eval x b c)

theorem mem_emptyRoutes (x : SatTy.denote) (q : DirectedRouteLookupCode.RecordTy.denote) :
    q∈emptyRoutes.eval x ↔ ∃ (i : Empty x) (r : Fin 4),routeRecord x (emptyEdge i r)=q := by
  rw [emptyRoutes_eval]
  simp only [List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨i,hi,r,he⟩
    exact ⟨i,r,he⟩
  · rintro ⟨i,r,he⟩
    exact ⟨i,empties_complete x i,r,he⟩

theorem mem_boundaryRoutes (x : SatTy.denote) (b : Bool) (q : DirectedRouteLookupCode.RecordTy.denote) :
    q∈(boundaryRoutes b).eval x ↔ ∃ (c : Cell x b) (r : Fin 4),routeRecord x (boundaryEdge b c r)=q := by
  rw [boundaryRoutes_eval]
  simp only [List.mem_flatMap,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨c,hc,r,he⟩
    exact ⟨c,r,he⟩
  · rintro ⟨c,r,he⟩
    exact ⟨c,cells_complete x b c,r,he⟩

def routes : Code SatTy RoutesTy := Code.append emptyRoutes
  (Code.append (boundaryRoutes true) (boundaryRoutes false))

theorem mem_routes (x : SatTy.denote) (q : DirectedRouteLookupCode.RecordTy.denote) :
    q∈routes.eval x ↔ ∃ e : Edge x,routeRecord x e=q := by
  rw [routes, append_eval, append_eval, List.mem_append,List.mem_append,
    mem_emptyRoutes,mem_boundaryRoutes,mem_boundaryRoutes]
  constructor
  · rintro (⟨i,r,he⟩ | ⟨c,r,he⟩ | ⟨c,r,he⟩)
    · exact ⟨emptyEdge i r,he⟩
    · exact ⟨boundaryEdge true c r,he⟩
    · exact ⟨boundaryEdge false c r,he⟩
  · rintro ⟨⟨i,r,p⟩,he⟩
    cases p with
    | unsplit h => exact Or.inl ⟨⟨i,h⟩,r,he⟩
    | above j h => exact Or.inr (Or.inl ⟨⟨(i,j),h⟩,r,he⟩)
    | below j h => exact Or.inr (Or.inr ⟨⟨(i,j),h⟩,r,he⟩)

def catalogueIndex (x : SatTy.denote) (e : Edge x) : SatWireDrawingGeometry.Edge x := .inr e

theorem routeRecord_actual (x : SatTy.denote) (e : Edge x) : routeRecord x e=
    ((SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.source x (catalogueIndex x e)),
      SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.target x (catalogueIndex x e))),
      (SatWireDrawingGeometry.route x (catalogueIndex x e)).map encodePoint) := rfl

/-- There are four lanes for each empty or extreme-column record. -/
theorem routes_length_le (x : SatTy.denote) : (routes.eval x).length≤36*x.length := by
  have he : (emptyRoutes.eval x).length=4*(empties x).length := by
    rw [emptyRoutes_eval,List.length_flatMap]
    simp [Nat.mul_comm]
  have hb (b : Bool) : ((boundaryRoutes b).eval x).length=4*(cells x b).length := by
    rw [boundaryRoutes_eval,List.length_flatMap]
    simp [Nat.mul_comm]
  rw [routes, append_eval, append_eval, List.length_append,List.length_append,he,hb,hb]
  have he := empties_length_le x
  have ht := cells_length_le x true
  have hf := cells_length_le x false
  omega

end GridHardness.SatResidualDrawingCode
