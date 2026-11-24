/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteDirectionsCode

/-!
# Lattice Route Endpoint Code

Bounded endpoint lookups and inward cardinal directions of encoded routes.
Absent points use the zero encoding; exact geometric specifications require
only the explicit indicated list-length bounds.
-/

@[expose] public section

namespace GridHardness.LatticeRouteCoreCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 600000

/-- Recover an encoded point componentwise, defaulting to the origin. -/
def pointAtCode : Code (.pair CycleInputTy .nat) PointTy :=
  .pair (.pair (lookupNat PointTy (.comp .fst .fst)) (lookupNat PointTy (.comp .fst .snd)))
    (.pair (lookupNat PointTy (.comp .snd .fst)) (lookupNat PointTy (.comp .snd .snd)))

theorem pointAtCode_eval (xs : CycleInputTy.denote) (i : Nat) (hi : i < xs.length) :
    pointAtCode.eval (xs,i)=xs[i] := by
  change (((lookupNat PointTy (.comp .fst .fst)).eval (xs,i),
    (lookupNat PointTy (.comp .fst .snd)).eval (xs,i)),
    ((lookupNat PointTy (.comp .snd .fst)).eval (xs,i),
    (lookupNat PointTy (.comp .snd .snd)).eval (xs,i)))=_
  rw [lookupNat_eval PointTy _ xs i hi,lookupNat_eval PointTy _ xs i hi,
    lookupNat_eval PointTy _ xs i hi,lookupNat_eval PointTy _ xs i hi]
  rfl

def headPointCode : Code CycleInputTy PointTy :=
  .comp (.pair .id (.const .nat 0)) pointAtCode

def lastPointCode : Code CycleInputTy PointTy :=
  .comp (.pair .id (.comp (.pair .listLen (.const .nat 1)) .natSub)) pointAtCode

theorem headPointCode_eval (xs : CycleInputTy.denote) (hl : 0 < xs.length) :
    headPointCode.eval xs=xs[0] := pointAtCode_eval xs 0 hl

theorem lastPointCode_eval (xs : CycleInputTy.denote) (hl : 0 < xs.length) :
    lastPointCode.eval xs=xs[xs.length-1]'(by omega) := pointAtCode_eval xs (xs.length-1) (by omega)

def initialDirectionCode : Code CycleInputTy .nat :=
  .comp (.pair headPointCode (.comp (.pair .id (.const .nat 1)) pointAtCode))
    LatticeRouteDirectionsCode.directionCode

def terminalDirectionCode : Code CycleInputTy .nat :=
  .comp (.pair lastPointCode
    (.comp (.pair .id (.comp (.pair .listLen (.const .nat 2)) .natSub)) pointAtCode))
      LatticeRouteDirectionsCode.directionCode

theorem initialDirectionCode_eval (xs : CycleInputTy.denote) (hl : 2 ≤ xs.length) :
    initialDirectionCode.eval xs=
      (LatticeRouteDirections.direction (decoded (xs[0]'(by omega))) (decoded (xs[1]'(by omega)))).val := by
  change LatticeRouteDirectionsCode.directionCode.eval (headPointCode.eval xs,pointAtCode.eval (xs,1))=_
  rw [headPointCode_eval xs (by omega),pointAtCode_eval xs 1 (by omega),
    LatticeRouteDirectionsCode.directionCode_eval]

theorem terminalDirectionCode_eval (xs : CycleInputTy.denote) (hl : 2 ≤ xs.length) :
    terminalDirectionCode.eval xs=
      (LatticeRouteDirections.direction (decoded (xs[xs.length-1]'(by omega)))
        (decoded (xs[xs.length-2]'(by omega)))).val := by
  change LatticeRouteDirectionsCode.directionCode.eval
    (lastPointCode.eval xs,pointAtCode.eval (xs,xs.length-2))=_
  rw [lastPointCode_eval xs (by omega),pointAtCode_eval xs _ (by omega),
    LatticeRouteDirectionsCode.directionCode_eval]

theorem initialDirectionCode_tangent (xs : CycleInputTy.denote) (hl : 2 ≤ xs.length) :
    initialDirectionCode.eval xs=(LatticeRouteDirections.tangent (xs.map decoded) false
      (by simpa only [List.length_map] using hl)).val := by
  rw [initialDirectionCode_eval xs hl]
  simp only [LatticeRouteDirections.tangent,LatticeRouteDirections.endpointPoint,
    LatticeRouteDirections.neighborPoint,LatticeRouteDirections.orient,Bool.false_eq_true,
    ite_false,List.getElem_map]

theorem terminalDirectionCode_tangent (xs : CycleInputTy.denote) (hl : 2 ≤ xs.length) :
    terminalDirectionCode.eval xs=(LatticeRouteDirections.tangent (xs.map decoded) true
      (by simpa only [List.length_map] using hl)).val := by
  rw [terminalDirectionCode_eval xs hl]
  simp only [LatticeRouteDirections.tangent,LatticeRouteDirections.endpointPoint,
    LatticeRouteDirections.neighborPoint,LatticeRouteDirections.orient,ite_true,
    List.getElem_reverse,List.getElem_map,List.length_map,Nat.sub_zero,Nat.sub_sub]

/-- Select either endpoint's point and inward direction. -/
def endpointPointCode : Code (.pair CycleInputTy .bool) PointTy :=
  .branch .snd (.comp .fst lastPointCode) (.comp .fst headPointCode)

def endpointDirectionCode : Code (.pair CycleInputTy .bool) .nat :=
  .branch .snd (.comp .fst terminalDirectionCode) (.comp .fst initialDirectionCode)

theorem endpointDirectionCode_eval (xs : CycleInputTy.denote) (b : Bool) (hl : 2 ≤ xs.length) :
    endpointDirectionCode.eval (xs,b)=(LatticeRouteDirections.tangent (xs.map decoded) b
      (by simpa only [List.length_map] using hl)).val := by
  cases b
  · rw [endpointDirectionCode,branch_eval_false _ _ rfl]
    exact initialDirectionCode_tangent xs hl
  · rw [endpointDirectionCode,branch_eval_true _ _ rfl]
    exact terminalDirectionCode_tangent xs hl

/-- Lookup preserves the input encoding; decoding identifies the exact endpoint. -/
theorem endpointPointCode_eval (xs : CycleInputTy.denote) (b : Bool) (hl : 2 ≤ xs.length) :
    decoded (endpointPointCode.eval (xs,b))=LatticeRouteDirections.endpointPoint (xs.map decoded) b
      (by simpa only [List.length_map] using hl) := by
  cases b
  · rw [endpointPointCode,branch_eval_false _ _ rfl]
    change decoded (headPointCode.eval xs)=_
    rw [headPointCode_eval xs (by omega)]
    simp only [LatticeRouteDirections.endpointPoint,LatticeRouteDirections.orient,
      Bool.false_eq_true,ite_false,List.getElem_map]
  · rw [endpointPointCode,branch_eval_true _ _ rfl]
    change decoded (lastPointCode.eval xs)=_
    rw [lastPointCode_eval xs (by omega)]
    simp only [LatticeRouteDirections.endpointPoint,LatticeRouteDirections.orient,
      ite_true,List.getElem_reverse,List.getElem_map,List.length_map,Nat.sub_zero]

/-- On canonical point lists the encoded endpoint agrees literally. -/
theorem endpointPointCode_encoded (xs : List (Int × Int)) (b : Bool) (hl : 2 ≤ xs.length) :
    endpointPointCode.eval (xs.map encodePoint,b)=
      encodePoint (LatticeRouteDirections.endpointPoint xs b hl) := by
  cases b
  · rw [endpointPointCode,branch_eval_false _ _ rfl]
    change headPointCode.eval (xs.map encodePoint)=_
    rw [headPointCode_eval _ (by simpa only [List.length_map] using
      (Nat.lt_of_lt_of_le (by decide : 0<2) hl))]
    simp only [LatticeRouteDirections.endpointPoint,LatticeRouteDirections.orient,
      Bool.false_eq_true,ite_false,List.getElem_map]
  · rw [endpointPointCode,branch_eval_true _ _ rfl]
    change lastPointCode.eval (xs.map encodePoint)=_
    rw [lastPointCode_eval _ (by simpa only [List.length_map] using
      (Nat.lt_of_lt_of_le (by decide : 0<2) hl))]
    simp only [LatticeRouteDirections.endpointPoint,LatticeRouteDirections.orient,
      ite_true,List.getElem_reverse,List.getElem_map,List.length_map,Nat.sub_zero]

theorem endpointDirectionCode_encoded (xs : List (Int × Int)) (b : Bool) (hl : 2 ≤ xs.length) :
    endpointDirectionCode.eval (xs.map encodePoint,b)=(LatticeRouteDirections.tangent xs b hl).val := by
  have hd : (xs.map encodePoint).map decoded=xs := by
    rw [List.map_map]
    simp only [Function.comp_def,GridAssembly.Encoding.decode_encode]
    exact List.map_id xs
  simpa only [hd] using endpointDirectionCode_eval (xs.map encodePoint) b
    (by simpa only [List.length_map] using hl)

end GridHardness.LatticeRouteCoreCode
