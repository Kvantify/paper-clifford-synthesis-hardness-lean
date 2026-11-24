/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseOrder
public import GridHardness.GridFrameCode
public import GridHardness.DirectedRouteLookupCode

/-!
# SAT Clause Body Code

A syntax-driven compiler for all clause-body points and internal routes.
The twelve vertices and fourteen lattice templates are fixed program data;
the only variable loop ranges over clause positions in the input formula.
-/

@[expose] public section

namespace GridHardness.SatClauseBodyCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000

abbrev ClauseTy := Ty.pair SatTy .nat
abbrev VertexRecordTy := Ty.pair .nat PointTy
abbrev VerticesTy := Ty.list VertexRecordTy
abbrev RoutesTy := DirectedRouteLookupCode.RecordsTy
abbrev OutputTy := Ty.pair VerticesTy RoutesTy

/-- Signed subtraction avoids any dependence on a well-formed index. -/
def baseCode : Code ClauseTy SignedTy :=
  .comp (.pair (Code.mul (.const .nat 3072) (.comp .fst .listLen))
    (Code.add (.const .nat 512) (Code.mul (.const .nat 1536) .snd))) normalize

theorem baseCode_eval (x : SatTy.denote) (c : Fin x.length) :
    baseCode.eval (x,c.val)=encodeInt (SatClauseOrder.base c) := by
  change normalize.eval (3072*x.length,512+1536*c.val)=_
  rw [normalize_eval,SatClauseOrder.base_eq]
  congr 1
  simp only [integer,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  ring

def frameCode : Code ClauseTy FrameTy :=
  .pair (.const .bool true) (.pair (.const .bool false) (.pair (.const .bool false)
    (.pair (.const SignedTy (encodeInt (-64))) baseCode)))

theorem frameCode_eval (x : SatTy.denote) (c : Fin x.length) :
    frameCode.eval (x,c.val)=encodeFrame (SatClausePlacement.frame (Fin.rev c)) := by
  change (true,false,false,encodeInt (-64),baseCode.eval (x,c.val))=_
  rw [baseCode_eval]
  rfl

def pointCode (v : Fin 12) : Code ClauseTy PointTy :=
  .comp (.pair frameCode (.const PointTy (encodePoint (PlanarSatClause.Lattice.point v))))
    GridFrameCode.point

theorem pointCode_eval (x : SatTy.denote) (c : Fin x.length) (v : Fin 12) :
    (pointCode v).eval (x,c.val)=encodePoint (SatClauseOrder.point c v) := by
  change GridFrameCode.point.eval (frameCode.eval (x,c.val),encodePoint _)=_
  rw [frameCode_eval,GridFrameCode.point_eval,decode_encodeFrame,GridAssembly.Encoding.decode_encode]
  rfl

def routeCode (e : Fin 14) : Code ClauseTy CycleInputTy :=
  .comp (.pair frameCode (.const CycleInputTy ((PlanarSatClause.Lattice.route e).map encodePoint)))
    (.listMapEnv GridFrameCode.point)

theorem routeCode_eval (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    (routeCode e).eval (x,c.val)=(SatClauseOrder.route c e).map encodePoint := by
  change ((PlanarSatClause.Lattice.route e).map encodePoint).map
    (fun q => GridFrameCode.point.eval (frameCode.eval (x,c.val),q))=_
  rw [frameCode_eval,List.map_map]
  change (PlanarSatClause.Lattice.route e).map _=
    ((PlanarSatClause.Lattice.route e).map (SatClausePlacement.frame (Fin.rev c)).map).map encodePoint
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_def]
  rw [GridFrameCode.point_eval,decode_encodeFrame,GridAssembly.Encoding.decode_encode]

abbrev label (x : SatTy.denote) (c : Fin x.length) (v : Fin 12) : Nat :=
  (PlanarSatCode.numbering ((vsOf x).length+1) x.length).num (clause c v)

def vertexRecord (x : SatTy.denote) (c : Fin x.length) (v : Fin 12) : VertexRecordTy.denote :=
  (label x c v,encodePoint (SatClauseOrder.point c v))

def routeRecord (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    DirectedRouteLookupCode.RecordTy.denote :=
  ((label x c (PlanarSatClause.Lattice.edge e).1,label x c (PlanarSatClause.Lattice.edge e).2),
    (SatClauseOrder.route c e).map encodePoint)

def vertexAt (v : Fin 12) : Code ClauseTy VertexRecordTy :=
  .pair (PlanarSatCode.clauseNum v.val) (pointCode v)

def routeAt (e : Fin 14) : Code ClauseTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair (PlanarSatCode.clauseNum (PlanarSatClause.Lattice.edge e).1.val)
    (PlanarSatCode.clauseNum (PlanarSatClause.Lattice.edge e).2.val)) (routeCode e)

theorem vertexAt_eval (x : SatTy.denote) (c : Fin x.length) (v : Fin 12) :
    (vertexAt v).eval (x,c.val)=vertexRecord x c v := by
  change ((PlanarSatCode.clauseNum v.val).eval (x,c.val),(pointCode v).eval (x,c.val))=_
  rw [PlanarSatCode.clauseNum_eval,pointCode_eval]
  rfl

theorem routeAt_eval (x : SatTy.denote) (c : Fin x.length) (e : Fin 14) :
    (routeAt e).eval (x,c.val)=routeRecord x c e := by
  change (((PlanarSatCode.clauseNum (PlanarSatClause.Lattice.edge e).1.val).eval (x,c.val),
    (PlanarSatCode.clauseNum (PlanarSatClause.Lattice.edge e).2.val).eval (x,c.val)),
    (routeCode e).eval (x,c.val))=_
  rw [PlanarSatCode.clauseNum_eval,PlanarSatCode.clauseNum_eval,routeCode_eval]
  rfl

def verticesAt : Code ClauseTy VerticesTy := PlanarSatCode.table (List.finRange 12) vertexAt
def routesAt : Code ClauseTy RoutesTy := PlanarSatCode.table (List.finRange 14) routeAt

def vertices : Code SatTy VerticesTy :=
  .comp (.pair .id PlanarSatCode.clauses) (.comp (.listMapEnv verticesAt) .listJoin)
def routes : Code SatTy RoutesTy :=
  .comp (.pair .id PlanarSatCode.clauses) (.comp (.listMapEnv routesAt) .listJoin)
def code : Code SatTy OutputTy := .pair vertices routes

theorem vertices_eval (x : SatTy.denote) : vertices.eval x=
    (List.finRange x.length).flatMap (fun c => (List.finRange 12).map (vertexRecord x c)) := by
  change ((PlanarSatCode.clauses.eval x).map (fun c => verticesAt.eval (x,c))).flatten=_
  rw [PlanarSatCode.clauses_finite,List.map_map,← List.flatMap_def]
  apply List.flatMap_congr
  intro c _
  simp only [Function.comp_def]
  rw [verticesAt,PlanarSatCode.table_eval]
  exact List.map_congr_left (fun v _ => vertexAt_eval x c v)

theorem routes_eval (x : SatTy.denote) : routes.eval x=
    (List.finRange x.length).flatMap (fun c => (List.finRange 14).map (routeRecord x c)) := by
  change ((PlanarSatCode.clauses.eval x).map (fun c => routesAt.eval (x,c))).flatten=_
  rw [PlanarSatCode.clauses_finite,List.map_map,← List.flatMap_def]
  apply List.flatMap_congr
  intro c _
  simp only [Function.comp_def]
  rw [routesAt,PlanarSatCode.table_eval]
  exact List.map_congr_left (fun e _ => routeAt_eval x c e)

theorem mem_vertices (x : SatTy.denote) (r : VertexRecordTy.denote) :
    r∈vertices.eval x ↔ ∃c v,r=vertexRecord x c v := by
  rw [vertices_eval]
  simp only [List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
  constructor
  · rintro ⟨c,v,h⟩; exact ⟨c,v,h.symm⟩
  · rintro ⟨c,v,h⟩; exact ⟨c,v,h.symm⟩

theorem mem_routes (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈routes.eval x ↔ ∃c e,r=routeRecord x c e := by
  rw [routes_eval]
  simp only [List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
  constructor
  · rintro ⟨c,e,h⟩; exact ⟨c,e,h.symm⟩
  · rintro ⟨c,e,h⟩; exact ⟨c,e,h.symm⟩

theorem vertices_length (x : SatTy.denote) : (vertices.eval x).length=12*x.length := by
  rw [vertices_eval,List.length_flatMap]
  simp [Nat.mul_comm]

theorem routes_length (x : SatTy.denote) : (routes.eval x).length=14*x.length := by
  rw [routes_eval,List.length_flatMap]
  simp [Nat.mul_comm]

end GridHardness.SatClauseBodyCode
