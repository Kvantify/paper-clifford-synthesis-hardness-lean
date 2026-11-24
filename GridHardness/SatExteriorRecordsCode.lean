/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatExteriorRouteCode

/-!
# SAT Exterior Records Code

Complete syntax-driven exterior records, including the separate empty
formula closing path. Every emitted key is the final graph's actual key.
-/

@[expose] public section

namespace GridHardness.SatExteriorRecordsCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatClauseBodyCode SatExteriorRouteCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 200000
attribute [local irreducible] actualLabel CorrectedSatInterval.PermutationWirePlacement.bodyVertex
  PlanarSatCode.varCount PlanarSatCode.varNum PlanarSatCode.clauseNum

def lastVariable : Code SatTy .nat :=
  .comp (.comp (.pair PlanarSatCode.varCount (.const .nat 1)) .natSub) (PlanarSatCode.varNum true)

def lastClause : Code SatTy .nat :=
  .comp (.pair .id (.comp (.pair .listLen (.const .nat 1)) .natSub)) (PlanarSatCode.clauseNum 1)

def sourceCode : Fin 6 → Code SatTy .nat
  | 0 => .const .nat 0
  | 1 => .const .nat 1
  | 2 => .const .nat 2
  | 3 => lastVariable
  | 4 => lastClause
  | 5 => lastVariable

def targetCode : Fin 6 → Code SatTy .nat
  | 0 => .const .nat 1
  | 1 => .const .nat 2
  | 2 => .const .nat 3
  | 3 => .comp (.pair .id (.const .nat 0)) (PlanarSatCode.clauseNum 8)
  | 4 => .const .nat 0
  | 5 => .const .nat 0

private theorem bodyLabel (x : SatTy.denote)
    (b : CorrectedSatInterval.PermutationWirePlacement.BodyVertex ((vsOf x).length +1) x.length) :
    actualLabel x (CorrectedSatInterval.PermutationWirePlacement.bodyVertex (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) b)=
      (PlanarSatCode.numbering ((vsOf x).length+1) x.length).num
        (CorrectedSatInterval.PermutationWirePlacement.bodyNames b) := by
  unfold actualLabel CorrectedSatInterval.PermutationWirePlacement.bodyVertex
  exact CorrectedSatInterval.PermutationGraph.original_names _ _ _

theorem sourceCode_eval (x : SatTy.denote) (e : SatExteriorDrawing.Edge x.length) :
    (sourceCode (tag e)).eval x=actualLabel x (SatExteriorDrawing.sourceVertex x e) := by
  rw [SatExteriorDrawing.sourceVertex,bodyLabel]
  cases e <;> simp only [tag,sourceCode,SatExteriorDrawing.source,
    CorrectedSatInterval.PermutationWirePlacement.bodyNames,PlanarSatCode.numbering_sent,
    PlanarSatCode.numbering_var,PlanarSatCode.numbering_clause]
  all_goals first | rfl | skip
  all_goals simp only [lastVariable,lastClause,Code.eval,PlanarSatCode.varNum_eval,
    PlanarSatCode.clauseNum_eval,PlanarSatCode.varCount_eval,
    SatExteriorDrawing.lastVar,CorrectedSatInterval.PermutationGraph.CoreEdges.Exterior.last,
    Bool.toNat_true,Nat.add_sub_cancel]
  all_goals rw [PlanarSatCode.clauseNum_eval]
  all_goals rfl

theorem targetCode_eval (x : SatTy.denote) (e : SatExteriorDrawing.Edge x.length) :
    (targetCode (tag e)).eval x=actualLabel x (SatExteriorDrawing.targetVertex x e) := by
  rw [SatExteriorDrawing.targetVertex,bodyLabel]
  cases e <;> simp only [tag,targetCode,SatExteriorDrawing.target,
    CorrectedSatInterval.PermutationWirePlacement.bodyNames,PlanarSatCode.numbering_sent,
    PlanarSatCode.numbering_var,PlanarSatCode.numbering_clause]
  all_goals first | rfl | skip
  all_goals simp only [Code.eval,PlanarSatCode.clauseNum_eval,
    SatExteriorDrawing.firstVar,CorrectedSatInterval.PermutationGraph.CoreEdges.Exterior.first]
  all_goals rw [PlanarSatCode.clauseNum_eval]
  all_goals rfl

noncomputable def record (x : SatTy.denote) (e : SatExteriorDrawing.Edge x.length) :
    DirectedRouteLookupCode.RecordTy.denote :=
  ((actualLabel x (SatExteriorDrawing.sourceVertex x e),
    actualLabel x (SatExteriorDrawing.targetVertex x e)),(SatExteriorDrawing.route x e).map encodePoint)

def recordAt (i : Fin 6) : Code SatTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair (sourceCode i) (targetCode i)) (SatExteriorRouteCode.route i)

theorem recordAt_eval (x : SatTy.denote) (e : SatExteriorDrawing.Edge x.length) :
    (recordAt (tag e)).eval x=record x e := by
  change (((sourceCode (tag e)).eval x,(targetCode (tag e)).eval x),
    (SatExteriorRouteCode.route (tag e)).eval x)=_
  rw [sourceCode_eval,targetCode_eval,SatExteriorRouteCode.route_eval]
  rfl

def edges (x : SatTy.denote) : List (SatExteriorDrawing.Edge x.length) :=
  [.sentinelFirst,.sentinelSecond,.firstVariable] ++
    if h : x.length=0 then [.closing h] else [.forward (by omega),.returning (by omega)]

theorem mem_edges (x : SatTy.denote) (e : SatExteriorDrawing.Edge x.length) : e∈edges x := by
  cases e with
  | sentinelFirst => simp [edges]
  | sentinelSecond => simp [edges]
  | firstVariable => simp [edges]
  | forward h => simp [edges,show x.length≠0 by omega]
  | returning h => simp [edges,show x.length≠0 by omega]
  | closing h => simp [edges,h]

def code : Code SatTy DirectedRouteLookupCode.RecordsTy :=
  Code.append (PlanarSatCode.table [(0:Fin 6),1,2] recordAt)
    (.branch (.comp (.pair .listLen (.const .nat 0)) .natEq)
      (PlanarSatCode.table [(5:Fin 6)] recordAt)
      (PlanarSatCode.table [(3:Fin 6),4] recordAt))

theorem code_eval (x : SatTy.denote) : code.eval x=(edges x).map (record x) := by
  have h0 : (recordAt 0).eval x=record x .sentinelFirst := recordAt_eval x .sentinelFirst
  have h1 : (recordAt 1).eval x=record x .sentinelSecond := recordAt_eval x .sentinelSecond
  have h2 : (recordAt 2).eval x=record x .firstVariable := recordAt_eval x .firstVariable
  simp only [code,append_eval,Code.eval,PlanarSatCode.table_eval,List.map_cons,List.map_nil,
    decide_eq_true_eq,edges,List.map_append,h0,h1,h2]
  by_cases h : x.length=0
  · have h5 : (recordAt 5).eval x=record x (.closing h) := recordAt_eval x (.closing h)
    simp only [dite_eq_left h,ite_eq_left h,h5,List.map_cons,List.map_nil]
  · have hp : 0<x.length := by omega
    have h3 : (recordAt 3).eval x=record x (.forward hp) := recordAt_eval x (.forward hp)
    have h4 : (recordAt 4).eval x=record x (.returning hp) := recordAt_eval x (.returning hp)
    simp only [dite_eq_right h,ite_eq_right h,h3,h4,List.map_cons,List.map_nil]

theorem mem_code (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈code.eval x ↔ ∃ e,r=record x e := by
  rw [code_eval,List.mem_map]
  constructor
  · rintro ⟨e,_,h⟩; exact ⟨e,h.symm⟩
  · rintro ⟨e,rfl⟩; exact ⟨e,mem_edges x e,rfl⟩

def catalogueIndex (x : SatTy.denote) (e : SatExteriorDrawing.Edge x.length) :
    SatWireDrawingGeometry.Edge x :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (.inr e))))))))

theorem record_actual (x : SatTy.denote) (e : SatExteriorDrawing.Edge x.length) :
    record x e=
      ((actualLabel x (SatWireDrawingGeometry.source x (catalogueIndex x e)),
        actualLabel x (SatWireDrawingGeometry.target x (catalogueIndex x e))),
        (SatWireDrawingGeometry.route x (catalogueIndex x e)).map encodePoint) := rfl

theorem emitted_arc (x : SatTy.denote) (e : SatExteriorDrawing.Edge x.length) :
    (SatClauseOrder.graph (finiteFormula x)).adj
      (SatExteriorDrawing.sourceVertex x e) (SatExteriorDrawing.targetVertex x e) :=
  SatExteriorDrawing.edge_is_arc x e

end GridHardness.SatExteriorRecordsCode
