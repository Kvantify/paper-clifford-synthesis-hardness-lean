/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetiredDrawingCatalogue
public import GridHardness.SatRetainedDrawingCode
public import GridHardness.SatClauseBoundaryCode

/-!
# SAT Last Link Code

The two links from the last crossing in every nonempty horizontal row
are compiled from the maximal crossing records of the SAT permutation.
-/

@[expose] public section

namespace GridHardness.SatLastLinkCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly CorrectedSatInterval SatRetirementGeometryCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000

abbrev CellTy := SatRetainedDrawingCode.CellTy
abbrev Cell (x : SatTy.denote) := SatLastLinkDrawing.LastCell (perm x)
abbrev RoutesTy := DirectedRouteLookupCode.RecordsTy

def encodeCell {x : SatTy.denote} (c : Cell x) : Nat×Nat := (c.val.1.val,c.val.2.val)

theorem last_correct (x : SatTy.denote) (i j : Fin (3 *x.length)) :
    (i.val,j.val)∈(SatClauseBoundaryCode.horizontal true).eval x ↔
      SatCrossingRetirement.Catalogue.lastRequest? (perm x) j=some i := by
  rw [SatClauseBoundaryCode.horizontal_correct,SatCrossingRetirement.Catalogue.lastRequest_correct]
  rfl

def cellListEquiv (x : SatTy.denote) :
    {c : Nat×Nat // c∈(SatClauseBoundaryCode.horizontal true).eval x} ≃ Cell x where
  toFun c := by
    have hm : c.val∈SatClauseOrderCode.crossings.eval x :=
      ((SatCrossingExtremaCode.mem_extrema true _ _).mp c.property).1
    have hb := SatClauseOrderCode.crossing_bounds x c.val hm
    exact ⟨(⟨c.val.1,hb.1⟩,⟨c.val.2,hb.2⟩),(last_correct x _ _).mp c.property⟩
  invFun c := ⟨encodeCell c,(last_correct x _ _).mpr c.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def cells (x : SatTy.denote) : List (Cell x) :=
  ((SatClauseBoundaryCode.horizontal true).eval x).attach.map (cellListEquiv x)

theorem cells_encoded (x : SatTy.denote) :
    (cells x).map encodeCell=(SatClauseBoundaryCode.horizontal true).eval x := by
  simp only [cells,List.map_map]
  change (((SatClauseBoundaryCode.horizontal true).eval x).attach.map Subtype.val)=_
  simpa only [id_eq,List.map_id] using
    (List.attach_map_val (l:=(SatClauseBoundaryCode.horizontal true).eval x) (f:=id))

theorem cells_complete (x : SatTy.denote) (c : Cell x) : c∈cells x :=
  List.mem_map.mpr ⟨(cellListEquiv x).symm c,List.mem_attach _ _,(cellListEquiv x).apply_symm_apply c⟩

def retired (v : Fin 8) : Code CellTy .nat :=
  .comp (.pair .fst (.comp .snd .snd)) (SatRetiredDrawingCode.labelCode v)

def sourceCode (b : Bool) : Code CellTy .nat :=
  if b then retired 7 else SatRetainedDrawingCode.labelCode (LastLinks.rowPort false)
def targetCode (b : Bool) : Code CellTy .nat :=
  if b then SatRetainedDrawingCode.labelCode (LastLinks.rowPort true) else retired 4

def routeCode (b : Bool) : Code CellTy CycleInputTy :=
  .comp (.pair SatRetainedDrawingCode.frameCode
    (.const CycleInputTy ((XorLine.Lattice.edgeRoute (SatLastLinkDrawing.localEdge b)).map encodePoint)))
    (.listMapEnv GridFrameCode.point)

theorem routeCode_eval (x : SatTy.denote) (c : Cell x) (b : Bool) :
    (routeCode b).eval (x,encodeCell c)=
      (SatLastLinkDrawing.route (perm x) (c,b)).map encodePoint := by
  change ((XorLine.Lattice.edgeRoute (SatLastLinkDrawing.localEdge b)).map encodePoint).map
    (fun q => GridFrameCode.point.eval (SatRetainedDrawingCode.frameCode.eval (x,encodeCell c),q))=_
  have hf := SatRetainedDrawingCode.frameCode_eval x (SatLastLinkDrawing.cell (c,b))
  change SatRetainedDrawingCode.frameCode.eval (x,encodeCell c)=_ at hf
  rw [hf,List.map_map]
  change (XorLine.Lattice.edgeRoute _).map _=
    ((XorLine.Lattice.edgeRoute _).map (SatCrossingLattice.frame (perm x) c.val).map).map encodePoint
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_def]
  rw [GridFrameCode.point_eval,decode_encodeFrame,GridAssembly.Encoding.decode_encode]
  rfl

theorem sourceCode_eval (x : SatTy.denote) (c : Cell x) (b : Bool) :
    (sourceCode b).eval (x,encodeCell c)=SatClauseBodyCode.actualLabel x
      (SatLastLinkDrawing.source (finiteFormula x) (perm x) (c,b)) := by
  cases b
  · change (SatRetainedDrawingCode.labelCode (LastLinks.rowPort false)).eval (x,encodeCell c)=_
    have he := SatRetainedDrawingCode.labelCode_eval x (SatLastLinkDrawing.cell (c,false)) (LastLinks.rowPort false)
    change _=SatClauseBodyCode.actualLabel x (PermutationWirePlacement.vertex _ _
      (.inr (SatLastLinkDrawing.cell (c,false),LastLinks.rowPort false)))
    rw [PermutationWirePlacement.vertex_fresh]
    exact he
  · change (SatRetiredDrawingCode.labelCode 7).eval (x,c.val.2.val)=_
    rw [SatRetiredDrawingCode.labelCode_eval]; rfl

theorem targetCode_eval (x : SatTy.denote) (c : Cell x) (b : Bool) :
    (targetCode b).eval (x,encodeCell c)=SatClauseBodyCode.actualLabel x
      (SatLastLinkDrawing.target (finiteFormula x) (perm x) (c,b)) := by
  cases b
  · change (SatRetiredDrawingCode.labelCode 4).eval (x,c.val.2.val)=_
    rw [SatRetiredDrawingCode.labelCode_eval]; rfl
  · change (SatRetainedDrawingCode.labelCode (LastLinks.rowPort true)).eval (x,encodeCell c)=_
    have he := SatRetainedDrawingCode.labelCode_eval x (SatLastLinkDrawing.cell (c,true)) (LastLinks.rowPort true)
    change _=SatClauseBodyCode.actualLabel x (PermutationWirePlacement.vertex _ _
      (.inr (SatLastLinkDrawing.cell (c,true),LastLinks.rowPort true)))
    rw [PermutationWirePlacement.vertex_fresh]
    exact he

def catalogueIndex (x : SatTy.denote) (c : Cell x) (b : Bool) :
    SatWireDrawingGeometry.Edge x := .inl (.inl (.inr (c,b)))

noncomputable def routeRecord (x : SatTy.denote) (c : Cell x) (b : Bool) :
    DirectedRouteLookupCode.RecordTy.denote :=
  ((SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.source x (catalogueIndex x c b)),
    SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.target x (catalogueIndex x c b))),
    (SatWireDrawingGeometry.route x (catalogueIndex x c b)).map encodePoint)

def routeAt (b : Bool) : Code CellTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair (sourceCode b) (targetCode b)) (routeCode b)

theorem routeAt_eval (x : SatTy.denote) (c : Cell x) (b : Bool) :
    (routeAt b).eval (x,encodeCell c)=routeRecord x c b := by
  change (((sourceCode b).eval (x,encodeCell c),(targetCode b).eval (x,encodeCell c)),
    (routeCode b).eval (x,encodeCell c))=_
  rw [sourceCode_eval,targetCode_eval,routeCode_eval]; rfl

def routesAt : Code CellTy RoutesTy := PlanarSatCode.table [false,true] routeAt
def code : Code SatTy RoutesTy :=
  .comp (.pair .id (SatClauseBoundaryCode.horizontal true)) (.comp (.listMapEnv routesAt) .listJoin)

attribute [local irreducible] SatClauseBoundaryCode.horizontal routesAt

theorem code_eval (x : SatTy.denote) : code.eval x=
    (cells x).flatMap (fun c => [false,true].map (routeRecord x c)) := by
  change (((SatClauseBoundaryCode.horizontal true).eval x).map (fun c => routesAt.eval (x,c))).flatten=_
  rw [← cells_encoded,List.map_map,← List.flatMap_def]
  apply List.flatMap_congr
  intro c _
  simp only [Function.comp_def]
  rw [routesAt,PlanarSatCode.table_eval]
  exact List.map_congr_left (fun b _ => routeAt_eval x c b)

theorem mem_code (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈code.eval x ↔ ∃c b,r=routeRecord x c b := by
  rw [code_eval]
  simp only [List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨c,_,b,_,h⟩; exact ⟨c,b,h.symm⟩
  · rintro ⟨c,b,rfl⟩
    exact ⟨c,cells_complete x c,b,by cases b <;> simp,rfl⟩

end GridHardness.SatLastLinkCode
