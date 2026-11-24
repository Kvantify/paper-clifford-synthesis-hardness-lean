/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBodyVertexCode
public import GridHardness.BoundedRangeCode

/-!
# SAT Variable Body Code

Direct variable branches and consecutive-variable backbone routes.
Route enumeration is fueled by a fixed expansion of the clause list.
-/

@[expose] public section

namespace GridHardness.SatVariableBodyCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatVariablePositionCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1200000

def lengthCode : Code SatVariablePositionCode.InputTy .nat :=
  .branch (.comp (.pair SatVariablePositionCode.count (.const .nat 0)) .natEq) (.const .nat 65)
    (.comp (.pair (Code.mul (.const .nat 512) SatVariablePositionCode.count) (.const .nat 63)) .natSub)

def samples : Code SatVariablePositionCode.InputTy (.list .nat) :=
  .comp (.pair (.comp .fst (SatAffineRangeCode.padding 1536 193)) lengthCode)
    (BoundedRangeCode.code .nat)

def samplePoint (backbone : Bool) : Code (.pair SatVariablePositionCode.InputTy .nat) PointTy :=
  .pair (.comp .fst xCode)
    (.comp (.pair
      (Code.add (Code.add (Code.mul (.const .nat 512)
        (.comp .fst (if backbone then Code.add prefixCode SatVariablePositionCode.count else prefixCode)))
        (.const .nat (if backbone then 64 else 128))) .snd) (.const .nat 0)) normalize)

def route (backbone : Bool) : Code SatVariablePositionCode.InputTy CycleInputTy :=
  .comp (.pair .id (if backbone then .const (.list .nat) (List.range 65) else samples))
    (.listMapEnv (samplePoint backbone))

theorem lengthCode_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    lengthCode.eval (x,v.val)=
      if SatVariableOrder.count (finiteFormula x) v=0 then 65
      else 512*SatVariableOrder.count (finiteFormula x) v-63 := by
  simp only [lengthCode,Code.mul,Code.eval]
  simp only [SatVariablePositionCode.count_eval x v,decide_eq_true_eq]

theorem lengthCode_bound (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    lengthCode.eval (x,v.val)≤1536*x.length+193 := by
  rw [lengthCode_eval x v]
  have h := SatVariableOrder.prefix_add_count_le (finiteFormula x) v
  split_ifs
  · exact Nat.le_trans (by decide : 65≤193) (Nat.le_add_left 193 _)
  · have hc : SatVariableOrder.count (finiteFormula x) v≤3*x.length := by omega
    calc
      _ ≤ 512*SatVariableOrder.count (finiteFormula x) v := Nat.sub_le _ _
      _ ≤ 512*(3*x.length) := Nat.mul_le_mul_left 512 hc
      _ ≤ 1536*x.length+193 := by omega

theorem samples_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    samples.eval (x,v.val)=List.range (lengthCode.eval (x,v.val)) := by
  change (BoundedRangeCode.code .nat).eval ((SatAffineRangeCode.padding 1536 193).eval x,_)=_
  apply BoundedRangeCode.code_eval_of_le
  rw [SatAffineRangeCode.padding_length]
  exact lengthCode_bound x v

theorem samplePoint_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) (k : Nat) (b : Bool) :
    (samplePoint b).eval ((x,v.val),k)=encodePoint
      (SatVariableLattice.wireX (3*x.length)+64,
        (if b then SatVariableLattice.exitY (SatVariableOrder.prefix (finiteFormula x) v+
          SatVariableOrder.count (finiteFormula x) v)
        else SatVariableLattice.entryY (SatVariableOrder.prefix (finiteFormula x) v))+(k:Int)) := by
  cases b <;> simp only [samplePoint,Code.add,Code.mul,Code.eval,Bool.false_eq_true,ite_false,ite_true]
  all_goals rw [xCode_eval,prefixCode_eval x v]
  · rw [normalize_eval]
    apply Prod.ext rfl
    congr 1
  · rw [SatVariablePositionCode.count_eval x v,normalize_eval]
    apply Prod.ext rfl
    congr 1

theorem direct_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    (route false).eval (x,v.val)=
      (SatVariableDrawing.route (finiteFormula x) (.direct v)).map encodePoint := by
  change (samples.eval (x,v.val)).map (fun k => (samplePoint false).eval ((x,v.val),k))=_
  rw [samples_eval x v,lengthCode_eval x v]
  simp only [SatVariableDrawing.route]
  split_ifs with h
  · simp only [SatVariableLattice.emptyRoute,SatCrossingRouting.rising,List.map_map,
      Function.comp_def,samplePoint_eval x v,Bool.false_eq_true,ite_false]
  · have hc : 0<SatVariableOrder.count (finiteFormula x) v := by omega
    have hl : (SatVariableLattice.exitY (SatVariableOrder.prefix (finiteFormula x) v+
        SatVariableOrder.count (finiteFormula x) v)-
        SatVariableLattice.entryY (SatVariableOrder.prefix (finiteFormula x) v)).toNat+1=
        512*SatVariableOrder.count (finiteFormula x) v-63 := by
      simp only [SatVariableLattice.exitY,SatVariableLattice.entryY,Nat.cast_add]
      omega
    simp only [SatVariableLattice.directRoute,SatCrossingRouting.rising,hl,List.map_map,
      Function.comp_def,samplePoint_eval x v,Bool.false_eq_true,ite_false]

theorem backbone_eval (x : SatTy.denote) (v w : Fin ((vsOf x).length +1)) (h : w.val =v.val +1) :
    (route true).eval (x,v.val)=
      (SatVariableDrawing.route (finiteFormula x) (.backbone v w h)).map encodePoint := by
  change (List.range 65).map (fun k => (samplePoint true).eval ((x,v.val),k))=_
  simp only [SatVariableDrawing.route,SatVariableLattice.backboneRoute,SatCrossingRouting.rising,
    List.map_map,Function.comp_def,samplePoint_eval x v,ite_true]

def recordAt (b : Bool) : Code SatVariablePositionCode.InputTy DirectedRouteLookupCode.RecordTy :=
  .pair (.pair (.comp .snd (PlanarSatCode.varNum b))
    (.comp (if b then Code.add .snd (.const .nat 1) else .snd) (PlanarSatCode.varNum (!b)))) (route b)

def recordsAt : Code SatVariablePositionCode.InputTy DirectedRouteLookupCode.RecordsTy :=
  Code.cons (recordAt false)
    (.branch (.comp (.pair (Code.add .snd (.const .nat 1)) (.comp .fst PlanarSatCode.varCount)) .natLt)
      (.comp (recordAt true) .listSingle) (.const DirectedRouteLookupCode.RecordsTy []))

def code : Code SatTy DirectedRouteLookupCode.RecordsTy :=
  .comp (.pair .id PlanarSatCode.variableIndices) (.comp (.listMapEnv recordsAt) .listJoin)

def record (x : SatTy.denote) (e : SatVariableDrawing.Edge ((vsOf x).length +1)) :
    DirectedRouteLookupCode.RecordTy.denote :=
  (((PlanarSatCode.varNum (SatVariableDrawing.endpoints e).1.2).eval (SatVariableDrawing.endpoints e).1.1.val,
    (PlanarSatCode.varNum (SatVariableDrawing.endpoints e).2.2).eval (SatVariableDrawing.endpoints e).2.1.val),
    (SatVariableDrawing.route (finiteFormula x) e).map encodePoint)

theorem recordAt_direct (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    (recordAt false).eval (x,v.val)=record x (.direct v) := by
  change (_, (route false).eval (x,v.val))=_
  rw [direct_eval]
  rfl

theorem recordAt_backbone (x : SatTy.denote) (v w : Fin ((vsOf x).length +1)) (h : w.val =v.val +1) :
    (recordAt true).eval (x,v.val)=record x (.backbone v w h) := by
  change (((PlanarSatCode.varNum true).eval v.val,(PlanarSatCode.varNum false).eval (v.val+1)),
    (route true).eval (x,v.val))=_
  rw [backbone_eval x v w h]
  simp only [record,SatVariableDrawing.endpoints,h]

def edgesAt (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    List (SatVariableDrawing.Edge ((vsOf x).length+1)) :=
  .direct v :: if h : v.val+1<(vsOf x).length+1 then [.backbone v ⟨v.val+1,h⟩ rfl] else []

def edges (x : SatTy.denote) : List (SatVariableDrawing.Edge ((vsOf x).length+1)) :=
  (List.finRange ((vsOf x).length+1)).flatMap (edgesAt x)

theorem recordsAt_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    recordsAt.eval (x,v.val)=(edgesAt x v).map (record x) := by
  simp only [recordsAt,Code.cons,Code.add,Code.eval,PlanarSatCode.varCount_eval]
  rw [CliffordComplexity.natLt_eval (v.val+1) ((vsOf x).length+1)]
  simp only [decide_eq_true_eq]
  change (recordAt false).eval (x,v.val)::
    (if v.val+1<(vsOf x).length+1 then [(recordAt true).eval (x,v.val)] else [])=_
  rw [recordAt_direct]
  unfold edgesAt
  split_ifs with h
  · rw [recordAt_backbone x v ⟨v.val+1,h⟩ rfl]
    rfl
  · rfl

theorem code_eval (x : SatTy.denote) : code.eval x=(edges x).map (record x) := by
  change ((PlanarSatCode.variableIndices.eval x).map (fun v => recordsAt.eval (x,v))).flatten=_
  rw [PlanarSatCode.variableIndices_finite,List.map_map,← List.flatMap_def]
  simp only [edges,List.map_flatMap]
  apply List.flatMap_congr
  exact fun v _ => recordsAt_eval x v

theorem mem_edges (x : SatTy.denote) (e : SatVariableDrawing.Edge ((vsOf x).length +1)) : e∈edges x := by
  apply List.mem_flatMap.mpr
  cases e with
  | direct v => exact ⟨v,List.mem_finRange _,by simp [edgesAt]⟩
  | backbone v w h =>
    refine ⟨v,List.mem_finRange _,?_⟩
    have hw : v.val+1<(vsOf x).length+1 := by omega
    have he : (⟨v.val+1,hw⟩ : Fin ((vsOf x).length+1))=w := Fin.ext h.symm
    simp only [edgesAt,dite_eq_left hw,he,List.mem_cons,List.mem_singleton]
    simp

end GridHardness.SatVariableBodyCode
