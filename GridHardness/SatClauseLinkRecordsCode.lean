/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseLinkGeometryCode
public import GridHardness.SatRetiredDrawingCode
public import GridHardness.SatRetainedDrawingCode

/-!
# SAT Clause Link Records Code

Full syntax-driven records for both directions of every clause-to-wire
link. The first crossing determines the wire label; an uncrossed wire uses
the original retired XOR port.
-/

@[expose] public section

namespace GridHardness.SatClauseLinkRecordsCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly CorrectedSatInterval SatClauseWireDrawing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 100000

attribute [local irreducible] SatRetiredDrawingCode.occurrenceCode SatClauseWireCode.firstAt
  SatRetainedDrawingCode.labelCode SatRetiredDrawingCode.labelCode SatClauseLinkGeometryCode.code

abbrev RowTy := SatClauseLinkGeometryCode.RowTy
abbrev perm (x : SatTy.denote) := SatClauseOrder.permutation (finiteFormula x)
abbrev occurrence (x : SatTy.denote) (j : Fin (3 *x.length)) :=
  (SatWireLayout.variableRank (finiteFormula x)).symm j

def clauseLabel (b : Bool) : Code RowTy .nat :=
  Code.add (.comp (.pair .fst (.comp SatRetiredDrawingCode.occurrenceCode .fst))
    (PlanarSatCode.clauseNum 0))
    (Code.add (Code.mul (.const .nat 4) (.comp SatRetiredDrawingCode.occurrenceCode .snd))
      (.const .nat (if b then 1 else 0)))

theorem clauseLabel_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) :
    (clauseLabel b).eval (x,j.val)=SatClauseBodyCode.actualLabel x
      (clauseVertex (finiteFormula x) (occurrence x j) b) := by
  change (PlanarSatCode.clauseNum 0).eval (x,(SatRetiredDrawingCode.occurrenceCode.eval (x,j.val)).1)+
    (4*(SatRetiredDrawingCode.occurrenceCode.eval (x,j.val)).2+(if b then 1 else 0))=_
  rw [SatRetiredDrawingCode.occurrenceCode_eval,PlanarSatCode.clauseNum_eval]
  rw [clauseVertex,SatClauseBodyCode.actualLabel_clause]
  simp only [SatClauseBodyCode.label,PlanarSatCode.numbering_clause,PlanarSatCode.occVal]
  have hp : (clausePort (occurrence x j) b).val=4*(occurrence x j).2.val+(if b then 1 else 0) := by
    rcases occurrence x j with ⟨c,k⟩
    fin_cases k <;> cases b <;> rfl
  rw [hp]
  simp only [occurrence,Nat.add_zero,Nat.add_assoc]

def crossingLabel (b : Bool) : Code RowTy .nat :=
  .comp (.pair .fst SatClauseWireCode.firstAt)
    (.comp (.listMapEnv (SatRetainedDrawingCode.labelCode (retainedPort b))) .listSum)

def wireLabel (b : Bool) : Code RowTy .nat :=
  .branch (Code.isNil SatClauseWireCode.firstAt)
    (SatRetiredDrawingCode.labelCode (if b then 7 else 4)) (crossingLabel b)

theorem wireLabel_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) :
    (wireLabel b).eval (x,j.val)=SatClauseBodyCode.actualLabel x
      (PermutationWirePlacement.vertex (finiteFormula x) (perm x) (wireVertex (perm x) j b)) := by
  cases hf : SatClauseWireLattice.firstRequest? (perm x) j with
  | none =>
    have he := (SatClauseWireCode.firstAt_empty x j).mpr hf
    change (if (Code.isNil SatClauseWireCode.firstAt).eval (x,j.val) then
      (SatRetiredDrawingCode.labelCode _).eval (x,j.val) else (crossingLabel b).eval (x,j.val))=_
    rw [ite_eq_left ((isNil_eval_true _ _).mpr he)]
    rw [SatRetiredDrawingCode.labelCode_eval,wireVertex_none _ _ _ hf]
    rfl
  | some i =>
    have he : SatClauseWireCode.firstAt.eval (x,j.val)=[(i.val,j.val)] := by
      rw [SatClauseWireCode.firstAt_correct]
      change (SatClauseWireLattice.firstRequest? (perm x) j).toList.map _=_
      rw [hf]; rfl
    change (if (Code.isNil SatClauseWireCode.firstAt).eval (x,j.val) then
      (SatRetiredDrawingCode.labelCode _).eval (x,j.val) else (crossingLabel b).eval (x,j.val))=_
    rw [ite_eq_right (by rw [isNil_eval_true,he]; simp)]
    change ((SatClauseWireCode.firstAt.eval (x,j.val)).map
      (fun c => (SatRetainedDrawingCode.labelCode (retainedPort b)).eval (x,c))).sum=_
    rw [he]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    let c : SatRetainedDrawingCode.Cell x := ⟨(i,j),(SatClauseWireLattice.firstRequest_sound _ _ _ hf).1⟩
    change (SatRetainedDrawingCode.labelCode (retainedPort b)).eval
      (x,SatRetainedDrawingCode.encodeCell c)=_
    rw [SatRetainedDrawingCode.labelCode_eval,wireVertex_some _ _ _ _ hf,
      PermutationWirePlacement.vertex_fresh]
    rfl

def routeAt (b : Bool) : Code RowTy DirectedRouteLookupCode.RecordTy :=
  .pair (if b then .pair (wireLabel b) (clauseLabel b) else .pair (clauseLabel b) (wireLabel b))
    (SatClauseLinkGeometryCode.code b)

noncomputable def record (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) :
    DirectedRouteLookupCode.RecordTy.denote :=
  ((SatClauseBodyCode.actualLabel x (source (finiteFormula x) (occurrence x j) b),
    SatClauseBodyCode.actualLabel x (target (finiteFormula x) (occurrence x j) b)),
    (route (finiteFormula x) (occurrence x j) b).map encodePoint)

theorem routeAt_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) :
    (routeAt b).eval (x,j.val)=record x j b := by
  have hr := SatClauseLinkGeometryCode.code_eval x j b
  have hc := clauseLabel_eval x j b
  have hw := wireLabel_eval x j b
  have hj : SatWireLayout.variableRank (finiteFormula x) (occurrence x j)=j :=
    Equiv.apply_symm_apply _ _
  cases b
  · change (((clauseLabel false).eval (x,j.val),(wireLabel false).eval (x,j.val)),
      (SatClauseLinkGeometryCode.code false).eval (x,j.val))=record x j false
    rw [hc,hw,hr]
    simp only [record,source,target,actualWireVertex,route,hj,Bool.false_eq_true,ite_false]
    rfl
  · change (((wireLabel true).eval (x,j.val),(clauseLabel true).eval (x,j.val)),
      (SatClauseLinkGeometryCode.code true).eval (x,j.val))=record x j true
    rw [hc,hw,hr]
    simp only [record,source,target,actualWireVertex,route,hj,ite_true]
    rfl

def routesAt : Code RowTy DirectedRouteLookupCode.RecordsTy :=
  PlanarSatCode.table [false,true] routeAt

def code : Code SatTy DirectedRouteLookupCode.RecordsTy :=
  .comp (.pair .id SatRetiredDrawingCode.rows) (.comp (.listMapEnv routesAt) .listJoin)

attribute [local irreducible] SatRetiredDrawingCode.rows routesAt

theorem code_eval (x : SatTy.denote) : code.eval x=
    (List.finRange (3*x.length)).flatMap (fun j => [record x j false,record x j true]) := by
  change ((SatRetiredDrawingCode.rows.eval x).map (fun j => routesAt.eval (x,j))).flatten=_
  rw [SatRetiredDrawingCode.rows_eval,List.map_map,←List.flatMap_def]
  apply List.flatMap_congr
  intro j _
  change routesAt.eval (x,j.val)=_
  rw [routesAt,PlanarSatCode.table_eval]
  simp only [List.map_cons,List.map_nil]
  rw [routeAt_eval x j false,routeAt_eval x j true]

theorem mem_code (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈code.eval x ↔ ∃ j : Fin (3*x.length),∃ b : Bool,r=record x j b := by
  rw [code_eval,List.mem_flatMap]
  simp only [List.mem_finRange,true_and,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  constructor
  · rintro ⟨j,h|h⟩
    · exact ⟨j,false,h⟩
    · exact ⟨j,true,h⟩
  · rintro ⟨j,b,rfl⟩
    cases b
    · exact ⟨j,Or.inl rfl⟩
    · exact ⟨j,Or.inr rfl⟩

theorem code_length (x : SatTy.denote) : (code.eval x).length=6*x.length := by
  rw [code_eval]
  simp [List.length_flatMap,Nat.mul_comm]
  omega

def catalogueIndex (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) :
    SatWireDrawingGeometry.Edge x := .inl (.inl (.inl (.inl (.inl (.inl (.inr (occurrence x j,b)))))))

theorem record_actual (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) :
    record x j b=((SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.source x (catalogueIndex x j b)),
      SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.target x (catalogueIndex x j b))),
      (SatWireDrawingGeometry.route x (catalogueIndex x j b)).map encodePoint) := rfl

end GridHardness.SatClauseLinkRecordsCode
