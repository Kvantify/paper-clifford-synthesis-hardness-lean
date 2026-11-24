/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseBodyCatalogue
public import GridHardness.BoundedRangeCode

/-!
# SAT Clause Backbone Code

The full records of the directed links between consecutive clause blocks.
The 505-point local template is fixed; clause enumeration and graph labels are
computed from the input syntax, including the zero- and one-clause cases.
-/

@[expose] public section

namespace GridHardness.SatClauseBackboneCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatClauseBodyCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

def template : CycleInputTy.denote :=
  (List.range 505).map (fun k : Nat => encodePoint (0,-4-(k:Int)))

def routeCode : Code SatClauseBodyCode.ClauseTy CycleInputTy :=
  .comp (.pair frameCode (.const CycleInputTy template)) (.listMapEnv GridFrameCode.point)

attribute [local irreducible] template frameCode

theorem routeCode_eval (x : SatTy.denote) (c : Fin x.length) :
    routeCode.eval (x,c.val)=(SatClauseBackbone.route c).map encodePoint := by
  change template.map (fun p => GridFrameCode.point.eval (frameCode.eval (x,c.val),p))=_
  rw [frameCode_eval]
  simp only [template,SatClauseBackbone.route,List.map_map]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_def]
  rw [GridFrameCode.point_eval,decode_encodeFrame,GridAssembly.Encoding.decode_encode]
  congr 1
  apply Prod.ext
  · rfl
  · change SatClauseOrder.base c+(-4-(k:Int))=SatClauseOrder.base c-4-k
    ring

def routeAt : Code SatClauseBodyCode.ClauseTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair (PlanarSatCode.clauseNum 1)
    (.comp (.pair .fst (Code.add .snd (.const .nat 1))) (PlanarSatCode.clauseNum 8))) routeCode

def record (x : SatTy.denote) (c d : Fin x.length) : DirectedRouteLookupCode.RecordTy.denote :=
  ((label x c 1,label x d 8),(SatClauseBackbone.route c).map encodePoint)

theorem routeAt_eval (x : SatTy.denote) (c d : Fin x.length) (h : d.val =c.val +1) :
    routeAt.eval (x,c.val)=record x c d := by
  change ((_,(PlanarSatCode.clauseNum 8).eval (x,c.val+1)),routeCode.eval (x,c.val))=_
  rw [←h,PlanarSatCode.clauseNum_eval,PlanarSatCode.clauseNum_eval,routeCode_eval]
  rfl

def indices : Code SatTy (.list .nat) :=
  .comp (.pair PlanarSatCode.clauses (.comp (.pair .listLen (.const .nat 1)) .natSub))
    (BoundedRangeCode.code .nat)

theorem indices_eval (x : SatTy.denote) : indices.eval x=List.range (x.length-1) := by
  change (BoundedRangeCode.code .nat).eval (PlanarSatCode.clauses.eval x,x.length-1)=_
  apply BoundedRangeCode.code_eval_of_le
  rw [PlanarSatCode.clauses_finite,List.length_map,List.length_finRange]
  omega

def code : Code SatTy DirectedRouteLookupCode.RecordsTy :=
  .comp (.pair .id indices) (.listMapEnv routeAt)

theorem code_eval (x : SatTy.denote) :
    code.eval x=(List.range (x.length-1)).map (fun c => routeAt.eval (x,c)) := by
  change (indices.eval x).map _=_
  rw [indices_eval]
  rfl

theorem mem_code (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈code.eval x ↔ ∃ c d : Fin x.length,d.val=c.val+1 ∧ r=record x c d := by
  rw [code_eval,List.mem_map]
  constructor
  · rintro ⟨i,hi,hr⟩
    have hi' := List.mem_range.mp hi
    let c : Fin x.length := ⟨i,by omega⟩
    let d : Fin x.length := ⟨i+1,by omega⟩
    exact ⟨c,d,rfl,hr.symm.trans (routeAt_eval x c d rfl)⟩
  · rintro ⟨c,d,hd,rfl⟩
    exact ⟨c.val,List.mem_range.mpr (by have := d.isLt; omega),routeAt_eval x c d hd⟩

theorem code_length (x : SatTy.denote) : (code.eval x).length=x.length-1 := by
  rw [code_eval,List.length_map,List.length_range]

def catalogueIndex (x : SatTy.denote) (c d : Fin x.length) (h : d.val =c.val +1) :
    SatWireDrawingGeometry.Edge x :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr (.backbone c d h)))))))))

theorem record_actual (x : SatTy.denote) (c d : Fin x.length) (h : d.val =c.val +1) :
    record x c d=
      ((actualLabel x (SatWireDrawingGeometry.source x (catalogueIndex x c d h)),
        actualLabel x (SatWireDrawingGeometry.target x (catalogueIndex x c d h))),
        (SatWireDrawingGeometry.route x (catalogueIndex x c d h)).map encodePoint) := by
  change record x c d=((actualLabel x (SatClauseOrder.vertex (finiteFormula x) c 1),
    actualLabel x (SatClauseOrder.vertex (finiteFormula x) d 8)),_)
  rw [actualLabel_clause,actualLabel_clause]
  rfl

theorem emitted_arc (x : SatTy.denote) (c d : Fin x.length) (h : d.val =c.val +1) :
    (SatClauseOrder.graph (finiteFormula x)).adj
      (SatClauseOrder.vertex (finiteFormula x) c 1)
      (SatClauseOrder.vertex (finiteFormula x) d 8) :=
  SatClauseDrawing.edge_is_arc (finiteFormula x) (.backbone c d h)

end GridHardness.SatClauseBackboneCode
