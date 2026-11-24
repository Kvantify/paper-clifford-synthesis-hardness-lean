/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatHorizontalDrawingCode
public import GridHardness.SatClauseInverseCode
public import GridHardness.SatVerticalCode

/-!
# SAT Vertical Drawing Code

Full vertical connector records compiled from SAT syntax. Both endpoint
labels recover the row from its permutation height by a certified scan.
-/

@[expose] public section

namespace GridHardness.SatVerticalDrawingCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatConnectorRouteCode LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

abbrev AtTy := Ty.pair SatTy SatCrossingConnectionCode.ConnectionTy
abbrev InputTy := Ty.pair SatTy SatVerticalCode.RecordTy
abbrev Edge := SatVerticalCode.Edge
abbrev RoutesTy := DirectedRouteLookupCode.RecordsTy

def lane (r : Fin 4) : Code AtTy SignedTy :=
  .comp (.pair (Code.add (Code.mul (.const .nat 512)
    (Code.add (.comp .snd (.comp .fst .snd)) (.const .nat 1))) (.const .nat 45))
    (.const .nat (30*r.val))) normalize

def level : Code AtTy SignedTy := natSigned
  (Code.add (Code.mul (.const .nat 512) (Code.add
    (Code.add (Code.mul (.const .nat 3) (.comp .fst .listLen)) (.const .nat 2))
    (.comp .snd (.comp .fst .fst)))) (.const .nat 10))

def height : Code AtTy .nat :=
  .comp (.pair (Code.mul (.const .nat 512) (.comp .snd (.comp .snd .fst)))
    (Code.add (Code.mul (.const .nat 512) (.comp .snd (.comp .fst .fst))) (.const .nat 20))) .natSub

def parameters (r : Fin 4) : Code AtTy SatConnectorRouteCode.BendTy :=
  .pair (.pair (lane r) level) height

def samples : Code AtTy (.list .nat) :=
  .comp (.pair (.comp .fst (SatAffineRangeCode.code 1536 0))
    (Code.add height (.const .nat 1))) (takeCode .nat)

def routeAt (r : Fin 4) : Code AtTy CycleInputTy :=
  .comp (.pair (parameters r) samples)
    (SatConnectorRouteCode.path (.comp (.pair (.comp .fst .fst) .snd) risingPoint) (decide (r.val%2=0)))

def connection (x : SatTy.denote) (e : Edge x) : SatCrossingConnectionCode.ConnectionTy.denote :=
  (SatVerticalCode.encode x e).1

theorem parameters_eval (x : SatTy.denote) (e : Edge x) :
    (parameters e.2).eval (x,connection x e)=
      (encodePoint (SatCrossingRouting.lane e.1.val.1 e.2,
        512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.1+10),
        (512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.2-10-
          (512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.1+10)).toNat) := by
  have hx : (lane e.2).eval (x,connection x e)=encodeInt (SatCrossingRouting.lane e.1.val.1 e.2) := by
    change normalize.eval (512*(e.1.val.1.val+1)+45,30*e.2.val)=_
    rw [normalize_eval]
    congr 1
  have hy : level.eval (x,connection x e)=encodeInt
      (512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.1+10) := by
    rw [level,natSigned_eval]
    congr 1
  have hh : height.eval (x,connection x e)=
      (512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.2-10-
        (512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.1+10)).toNat := by
    change 512*((SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.2).val-
      (512*((SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.1).val+20)=_
    unfold PermutationWireLayout.high
    omega
  change (((lane e.2).eval (x,connection x e),level.eval (x,connection x e)),height.eval (x,connection x e))=_
  rw [hx,hy,hh]
  rfl

theorem samples_eval (x : SatTy.denote) (e : Edge x) :
    samples.eval (x,connection x e)=List.range
      ((512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.2-10-
        (512*PermutationWireLayout.high (SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.1+10)).toNat+1) := by
  have hh := congrArg Prod.snd (parameters_eval x e)
  change height.eval (x,connection x e)=_ at hh
  have hl := (SatVerticalDrawing.route_length (SatClauseOrder.permutation (finiteFormula x)) e).2
  unfold SatVerticalDrawing.route SatCrossingRouting.route at hl
  split_ifs at hl <;> simp only [List.length_reverse,SatCrossingRouting.corridor,SatCrossingRouting.rising_length] at hl
  all_goals
    change (takeCode .nat).eval ((SatAffineRangeCode.code 1536 0).eval x,height.eval (x,connection x e)+1)=_
    rw [takeCode_eval,SatAffineRangeCode.code_eval,Nat.add_zero,hh,List.take_range,
      Nat.min_eq_left (by nlinarith)]

theorem routeAt_eval (x : SatTy.denote) (e : Edge x) :
    (routeAt e.2).eval (x,connection x e)=
      (SatVerticalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e).map encodePoint := by
  change (SatConnectorRouteCode.path _ (decide (e.2.val%2=0))).eval
    ((parameters e.2).eval (x,connection x e),samples.eval (x,connection x e))=_
  rw [parameters_eval,samples_eval,SatConnectorRouteCode.path_eval]
  change (if decide (e.2.val%2=0) then
      ((List.range _).map (fun k => risingPoint.eval (encodePoint _,k))).reverse
    else (List.range _).map (fun k => risingPoint.eval (encodePoint _,k)))=_
  rw [rising_map]
  unfold SatVerticalDrawing.route SatCrossingRouting.route SatCrossingRouting.corridor
  by_cases h : e.2.val%2=0 <;> simp [h,List.map_reverse]

def lowerRow : Code AtTy .nat :=
  .comp (.pair .fst (.comp .snd (.comp .fst .fst))) SatClauseInverseCode.code

def upperRow : Code AtTy .nat :=
  .comp (.pair .fst (.comp .snd (.comp .snd .fst))) SatClauseInverseCode.code

def portLabel (upper : Bool) (v : SatCrossingHorizontal.RetainedVertex) : Code AtTy .nat :=
  .comp (.pair .fst (.pair (.comp .snd (.comp .fst .snd))
    (if upper then upperRow else lowerRow))) (SatRetainedDrawingCode.labelCode v)

theorem portLabel_eval (x : SatTy.denote) (e : Edge x)
    (upper : Bool) (v : SatCrossingHorizontal.RetainedVertex) :
    (portLabel upper v).eval (x,connection x e)=
      SatRetainedDrawingCode.label x
        (if upper then SatVerticalDrawing.upperCell e.1 else SatVerticalDrawing.lowerCell e.1) v := by
  have hlo : lowerRow.eval (x,connection x e)=e.1.val.2.1.val :=
    SatClauseInverseCode.code_eval x e.1.val.2.1
  have hup : upperRow.eval (x,connection x e)=e.1.val.2.2.val :=
    SatClauseInverseCode.code_eval x e.1.val.2.2
  cases upper
  · change (SatRetainedDrawingCode.labelCode v).eval (x,(e.1.val.1.val,lowerRow.eval (x,connection x e)))=_
    rw [hlo]
    exact SatRetainedDrawingCode.labelCode_eval x (SatVerticalDrawing.lowerCell e.1) v
  · change (SatRetainedDrawingCode.labelCode v).eval (x,(e.1.val.1.val,upperRow.eval (x,connection x e)))=_
    rw [hup]
    exact SatRetainedDrawingCode.labelCode_eval x (SatVerticalDrawing.upperCell e.1) v

def fixedRecord (r : Fin 4) : Code AtTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair (portLabel (decide (r.val%2=0)) (SatVerticalDrawing.outputPort r))
    (portLabel (!decide (r.val%2=0)) (SatVerticalDrawing.inputPort r))) (routeAt r)

def recordAt : Code InputTy DirectedRouteLookupCode.RecordTy :=
  let z : Code InputTy AtTy := .pair .fst (.comp .snd .fst)
  let tag : Code InputTy .nat := .comp .snd .snd
  .branch (.comp (.pair tag (.const .nat 0)) .natEq) (.comp z (fixedRecord 0))
    (.branch (.comp (.pair tag (.const .nat 1)) .natEq) (.comp z (fixedRecord 1))
      (.branch (.comp (.pair tag (.const .nat 2)) .natEq) (.comp z (fixedRecord 2))
        (.comp z (fixedRecord 3))))

noncomputable def routeRecord (x : SatTy.denote) (e : Edge x) : DirectedRouteLookupCode.RecordTy.denote :=
  ((SatClauseBodyCode.actualLabel x (SatVerticalDrawing.source (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e),
    SatClauseBodyCode.actualLabel x (SatVerticalDrawing.target (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e)),
    (SatVerticalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e).map encodePoint)

theorem fixedRecord_eval (x : SatTy.denote) (e : Edge x) :
    (fixedRecord e.2).eval (x,connection x e)=routeRecord x e := by
  change (((portLabel _ _).eval (x,connection x e),(portLabel _ _).eval (x,connection x e)),
    (routeAt e.2).eval (x,connection x e))=_
  rw [portLabel_eval,portLabel_eval,routeAt_eval]
  unfold routeRecord SatVerticalDrawing.source SatVerticalDrawing.target SatVerticalDrawing.endpoints
  by_cases h : e.2.val%2=0 <;>
    simp [h,SatRetainedDrawingCode.label,SatRetainedDrawing.vertex]

theorem recordAt_eval (x : SatTy.denote) (e : Edge x) :
    recordAt.eval (x,SatVerticalCode.encode x e)=routeRecord x e := by
  have he : recordAt.eval (x,SatVerticalCode.encode x e)=(fixedRecord e.2).eval (x,connection x e) := by
    obtain ⟨c,r⟩ := e
    fin_cases r <;> rfl
  rw [he,fixedRecord_eval]

def routes : Code SatTy RoutesTy :=
  .comp (.pair .id SatVerticalCode.records) (.listMapEnv recordAt)

attribute [local irreducible] SatVerticalCode.records recordAt

theorem mem_routes (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈routes.eval x ↔ ∃ e : Edge x, routeRecord x e=r := by
  change r∈(SatVerticalCode.records.eval x).map (fun a => recordAt.eval (x,a)) ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    obtain ⟨e,rfl⟩ := (SatVerticalCode.records_correct x a).mp ha
    exact ⟨e,(recordAt_eval x e).symm.trans he⟩
  · rintro ⟨e,rfl⟩
    exact ⟨SatVerticalCode.encode x e,SatVerticalCode.encoded_edge_mem x e,recordAt_eval x e⟩

end GridHardness.SatVerticalDrawingCode
