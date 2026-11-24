/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatConnectorRouteCode
public import GridHardness.SatRetainedDrawingCode
public import GridHardness.SatHorizontalCode
public import GridHardness.SatAffineRangeCode

/-!
# SAT Horizontal Drawing Code

Full horizontal connector records, including chronological vertex labels
and every signed lattice point, compiled from the SAT syntax.
-/

@[expose] public section

namespace GridHardness.SatHorizontalDrawingCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatConnectorRouteCode LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
attribute [local irreducible] SatCrossingTraceCode.rankValue

abbrev AtTy := Ty.pair SatTy SatCrossingConnectionCode.ConnectionTy
abbrev InputTy := Ty.pair SatTy SatHorizontalCode.RecordTy
abbrev Edge (x : SatTy.denote) := SatHorizontalDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))
abbrev RoutesTy := DirectedRouteLookupCode.RecordsTy

def startX : Code AtTy SignedTy := natSigned
  (Code.add (Code.mul (.const .nat 512) (Code.add (.comp .snd (.comp .fst .fst)) (.const .nat 1)))
    (.const .nat 45))
def level : Code AtTy SignedTy := natSigned
  (Code.mul (.const .nat 512) (Code.add
    (Code.add (Code.mul (.const .nat 3) (.comp .fst .listLen)) (.const .nat 2))
    (.comp (.pair .fst (.comp .snd (.comp .fst .snd))) SatCrossingTraceCode.rankValue)))
def gap : Code AtTy .nat :=
  .comp (.pair (Code.mul (.const .nat 512) (.comp .snd (.comp .snd .fst)))
    (Code.add (Code.mul (.const .nat 512) (.comp .snd (.comp .fst .fst))) (.const .nat 120))) .natSub

def parameters : Code AtTy SatConnectorRouteCode.BendTy := .pair (.pair startX level) gap

def samples : Code AtTy (.list .nat) :=
  .comp (.pair (.comp .fst (SatAffineRangeCode.code 1536 0))
    (Code.add gap (.const .nat 17))) (takeCode .nat)

def routeAt (b : Bool) : Code AtTy CycleInputTy :=
  .comp (.pair parameters samples)
    (SatConnectorRouteCode.path (if b then SatConnectorRouteCode.bendPoint else reflectedPoint) (!b))

def connection {x : SatTy.denote} (e : Edge x) : SatCrossingConnectionCode.ConnectionTy.denote :=
  (SatHorizontalCode.encode e).1

theorem parameters_eval (x : SatTy.denote) (e : Edge x) :
    parameters.eval (x,connection e)=
      (encodePoint (512*PermutationWireLayout.low e.1.val.1+45,
        512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.2),
        SatCrossingHorizontal.gapLength e.1.val.1 e.1.val.2.1) := by
  have hx : startX.eval (x,connection e)=encodeInt (512*PermutationWireLayout.low e.1.val.1+45) := by
    rw [startX,natSigned_eval]
    congr 1
  have hy : level.eval (x,connection e)=encodeInt
      (512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.2) := by
    rw [level,natSigned_eval]
    change encodeInt (512*(3*x.length+2+SatCrossingTraceCode.rankValue.eval (x,e.1.val.2.2.val)):Nat)=_
    rw [SatCrossingTraceCode.rankValue_eval]
    congr 1
  have hg : gap.eval (x,connection e)=SatCrossingHorizontal.gapLength e.1.val.1 e.1.val.2.1 := by
    change 512*e.1.val.2.1.val-(512*e.1.val.1.val+120)=_
    unfold SatCrossingHorizontal.gapLength PermutationWireLayout.low
    omega
  change ((startX.eval (x,connection e),level.eval (x,connection e)),gap.eval (x,connection e))=_
  rw [hx,hy,hg]
  rfl

theorem samples_eval (x : SatTy.denote) (e : Edge x) :
    samples.eval (x,connection e)=
      List.range (SatCrossingHorizontal.gapLength e.1.val.1 e.1.val.2.1+17) := by
  have hg : gap.eval (x,connection e)=SatCrossingHorizontal.gapLength e.1.val.1 e.1.val.2.1 :=
    congrArg Prod.snd (parameters_eval x e)
  have hl := (SatCrossingHorizontal.route_length_bounds
    (SatClauseOrder.permutation (finiteFormula x)) e.1.val.1 e.1.val.2.1 e.1.val.2.2 e.1.property.2.2.1).2.1
  rw [SatCrossingHorizontal.upperRoute,SatCrossingHorizontal.upperPath_length] at hl
  change (takeCode .nat).eval ((SatAffineRangeCode.code 1536 0).eval x,gap.eval (x,connection e)+17)=_
  rw [takeCode_eval,SatAffineRangeCode.code_eval,Nat.add_zero,hg,List.take_range,
    Nat.min_eq_left (by nlinarith)]

theorem routeAt_eval (x : SatTy.denote) (e : Edge x) :
    (routeAt e.2).eval (x,connection e)=
      (SatHorizontalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e).map encodePoint := by
  change (SatConnectorRouteCode.path _ (!e.2)).eval
    (parameters.eval (x,connection e),samples.eval (x,connection e))=_
  rw [parameters_eval,samples_eval,SatConnectorRouteCode.path_eval]
  cases hb : e.2
  · simp only [Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
    simp only [SatHorizontalDrawing.route,SatCrossingHorizontal.connectionRoute,hb,
      Bool.false_eq_true,ite_false,SatCrossingHorizontal.lowerRoute]
    exact lower_map _ _ _
  · simp only [Bool.not_true,ite_true,Bool.false_eq_true,ite_false]
    simp only [SatHorizontalDrawing.route,SatCrossingHorizontal.connectionRoute,hb,
      ite_true,SatCrossingHorizontal.upperRoute]
    exact upper_map _ _ _

def oldLabel (b : Bool) : Code AtTy .nat :=
  .comp (.pair .fst (.comp .snd .fst)) (SatRetainedDrawingCode.labelCode (SatHorizontalDrawing.oldPort b))
def newLabel (b : Bool) : Code AtTy .nat :=
  .comp (.pair .fst (.comp .snd .snd)) (SatRetainedDrawingCode.labelCode (SatHorizontalDrawing.newPort b))

def fixedRecord (b : Bool) : Code AtTy DirectedRouteLookupCode.RecordTy :=
  .pair (if b then .pair (oldLabel b) (newLabel b) else .pair (newLabel b) (oldLabel b)) (routeAt b)
def recordAt : Code InputTy DirectedRouteLookupCode.RecordTy :=
  .branch (.comp .snd .snd)
    (.comp (.pair .fst (.comp .snd .fst)) (fixedRecord true))
    (.comp (.pair .fst (.comp .snd .fst)) (fixedRecord false))

noncomputable def routeRecord (x : SatTy.denote) (e : Edge x) : DirectedRouteLookupCode.RecordTy.denote :=
  ((SatClauseBodyCode.actualLabel x (SatHorizontalDrawing.source (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e),
    SatClauseBodyCode.actualLabel x (SatHorizontalDrawing.target (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e)),
    (SatHorizontalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e).map encodePoint)

theorem recordAt_eval (x : SatTy.denote) (e : Edge x) :
    recordAt.eval (x,SatHorizontalCode.encode e)=routeRecord x e := by
  have ho (b : Bool) : (oldLabel b).eval (x,connection e)=
      SatRetainedDrawingCode.label x (SatHorizontalDrawing.oldCell e.1) (SatHorizontalDrawing.oldPort b) := by
    exact SatRetainedDrawingCode.labelCode_eval x (SatHorizontalDrawing.oldCell e.1) (SatHorizontalDrawing.oldPort b)
  have hn (b : Bool) : (newLabel b).eval (x,connection e)=
      SatRetainedDrawingCode.label x (SatHorizontalDrawing.newCell e.1) (SatHorizontalDrawing.newPort b) := by
    exact SatRetainedDrawingCode.labelCode_eval x (SatHorizontalDrawing.newCell e.1) (SatHorizontalDrawing.newPort b)
  have hr := routeAt_eval x e
  cases hb : e.2 <;>
    simp only [recordAt,Code.eval,SatHorizontalCode.encode,hb,Bool.false_eq_true,ite_false,ite_true]
  all_goals
    change (fixedRecord _).eval (x,connection e)=_
    unfold fixedRecord
    simp only [Bool.false_eq_true,ite_false,ite_true,Code.eval]
    rw [ho,hn,← hb,hr]
    simp only [routeRecord,SatHorizontalDrawing.source,SatHorizontalDrawing.target,
      SatHorizontalDrawing.endpoints,hb,Bool.false_eq_true,ite_false,ite_true,
      SatRetainedDrawingCode.label,SatRetainedDrawing.vertex]

def routes : Code SatTy RoutesTy :=
  .comp (.pair .id SatHorizontalCode.records) (.listMapEnv recordAt)

attribute [local irreducible] SatHorizontalCode.records recordAt

theorem mem_routes (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈routes.eval x ↔ ∃ e : Edge x, routeRecord x e=r := by
  change r∈(SatHorizontalCode.records.eval x).map (fun a => recordAt.eval (x,a)) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    obtain ⟨e,rfl⟩ := (SatHorizontalCode.records_correct x a).mp ha
    exact ⟨e,(recordAt_eval x e).symm.trans he⟩
  · rintro ⟨e,rfl⟩
    exact ⟨SatHorizontalCode.encode e,SatHorizontalCode.encoded_edge_mem x e,recordAt_eval x e⟩

end GridHardness.SatHorizontalDrawingCode
