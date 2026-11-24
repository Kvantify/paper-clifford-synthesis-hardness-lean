/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariablePositionCode

/-!
# SAT Body Vertex Code

Explicit original-body vertex records, carrying the final sweep graph's
unchanged original labels and its common geometric coordinates.
-/

@[expose] public section

namespace GridHardness.SatBodyVertexCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatClauseBodyCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000

def variableAt (b : Bool) : Code SatVariablePositionCode.InputTy VertexRecordTy :=
  .pair (.comp .snd (PlanarSatCode.varNum b)) (SatVariablePositionCode.point b)

def variablesAt : Code SatVariablePositionCode.InputTy VerticesTy :=
  PlanarSatCode.table [false,true] variableAt

def variableRecords : Code SatTy VerticesTy :=
  .comp (.pair .id PlanarSatCode.variableIndices) (.comp (.listMapEnv variablesAt) .listJoin)

def variableRecord (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) (b : Bool) :
    VertexRecordTy.denote :=
  (3+(v.val*2+b.toNat),encodePoint (SatVariablePlacement.point (finiteFormula x) v b))

theorem variableAt_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) (b : Bool) :
    (variableAt b).eval (x,v.val)=variableRecord x v b := by
  change ((PlanarSatCode.varNum b).eval v.val,(SatVariablePositionCode.point b).eval (x,v.val))=_
  rw [PlanarSatCode.varNum_eval,SatVariablePositionCode.point_eval]
  rfl

theorem variables_eval (x : SatTy.denote) : variableRecords.eval x=
    (List.finRange ((vsOf x).length+1)).flatMap
      (fun v => [variableRecord x v false,variableRecord x v true]) := by
  change ((PlanarSatCode.variableIndices.eval x).map (fun v => variablesAt.eval (x,v))).flatten=_
  rw [PlanarSatCode.variableIndices_finite,List.map_map,← List.flatMap_def]
  apply List.flatMap_congr
  intro v _
  simp only [Function.comp_def,variablesAt,PlanarSatCode.table_eval,List.map_cons,List.map_nil,
    variableAt_eval x v]

theorem variableRecord_actual (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) (b : Bool) :
    variableRecord x v b=
      (actualLabel x (SatVariableDrawing.vertex (finiteFormula x)
        (SatClauseOrder.permutation (finiteFormula x)) (v,b)),
      encodePoint (SatGlobalVertexPlacement.actualPoint (finiteFormula x)
        (SatVariableDrawing.vertex (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) (v,b)))) := by
  unfold variableRecord SatVariableDrawing.vertex actualLabel
  rw [CorrectedSatInterval.PermutationGraph.original_names,PlanarSatCode.numbering_var,
    SatGlobalVertexPlacement.actualPoint_variable]

def sentinelPoint (i : Fin 3) : Code SatTy PointTy :=
  if i=2 then .pair (.comp (.pair .id (.const .nat 0)) SatVariablePositionCode.xCode)
    (.const SignedTy (encodeInt (-64)))
  else .const PointTy (encodePoint (if i=0 then (-128,0) else (-128,-64)))

theorem sentinelPoint_eval (x : SatTy.denote) (i : Fin 3) :
    (sentinelPoint i).eval x=encodePoint (SatExteriorLattice.sentinel (3*x.length) i) := by
  fin_cases i <;> simp only [sentinelPoint,Fin.isValue,show ¬(0:Fin 3)=2 from by decide,
    show ¬(1:Fin 3)=2 from by decide,show ¬(1:Fin 3)=0 from by decide,ite_false,ite_true]
  · rfl
  · rfl
  · change (SatVariablePositionCode.xCode.eval (x,0),encodeInt (-64))=_
    rw [SatVariablePositionCode.xCode_eval]
    rfl

def sentinelAt (i : Fin 3) : Code SatTy VertexRecordTy :=
  .pair (.const .nat i.val) (sentinelPoint i)

def sentinels : Code SatTy VerticesTy := PlanarSatCode.table (List.finRange 3) sentinelAt

theorem sentinels_eval (x : SatTy.denote) : sentinels.eval x=
    (List.finRange 3).map (fun i => (i.val,encodePoint (SatExteriorLattice.sentinel (3*x.length) i))) := by
  rw [sentinels,PlanarSatCode.table_eval]
  apply List.map_congr_left
  intro i _
  change (i.val,(sentinelPoint i).eval x)=_
  rw [sentinelPoint_eval]

theorem sentinel_actual (x : SatTy.denote) (i : Fin 3) :
    (i.val,encodePoint (SatExteriorLattice.sentinel (3*x.length) i))=
      (actualLabel x (CorrectedSatInterval.PermutationGraph.liftOriginal (finiteFormula x)
        (SatClauseOrder.permutation (finiteFormula x)) (sent i)),
      encodePoint (SatGlobalVertexPlacement.actualPoint (finiteFormula x)
        (CorrectedSatInterval.PermutationGraph.liftOriginal (finiteFormula x)
          (SatClauseOrder.permutation (finiteFormula x)) (sent i)))) := by
  unfold actualLabel
  rw [CorrectedSatInterval.PermutationGraph.original_names,PlanarSatCode.numbering_sent,
    SatGlobalVertexPlacement.actualPoint_sentinel]

def code : Code SatTy VerticesTy := Code.append sentinels variableRecords

theorem length (x : SatTy.denote) :
    (code.eval x).length=3+2*((vsOf x).length+1) := by
  change (sentinels.eval x++variableRecords.eval x).length=_
  rw [List.length_append,sentinels_eval,variables_eval,List.length_flatMap]
  simp [Nat.mul_comm]

end GridHardness.SatBodyVertexCode
