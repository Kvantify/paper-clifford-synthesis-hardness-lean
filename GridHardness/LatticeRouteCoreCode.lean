/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteSubdivisionCode
public import GridHardness.LatticeRouteCore

/-!
# Lattice Route Core Code

Polynomial-cost orientation, fixed subdivision and asymmetric corridor
cuts. The terminal cut is a binary input; it only restricts an explicit list.
The dilation factor and initial cut are fixed program parameters.
-/

@[expose] public section

namespace GridHardness.LatticeRouteCoreCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev CoreInputTy := Ty.pair CycleInputTy .nat
abbrev OrientedInputTy := Ty.pair CycleInputTy (.pair .bool .nat)

/-- Subdivide a route at fixed scale, then remove its endpoint cuts. -/
def coreCode (s a : Nat) : Code CoreInputTy CycleInputTy :=
  .comp (.pair (.comp .fst (subdivideCode s)) .snd) (trimCode PointTy a)

theorem coreCode_eval (s a b : Nat) (xs : CycleInputTy.denote) :
    (coreCode s a).eval (xs,b)=
      (LatticeRouteCore.core s a b (xs.map decoded)).map encodePoint := by
  change (trimCode PointTy a).eval ((subdivideCode s).eval xs,b)=_
  rw [trimCode_eval,subdivideCode_eval,trim_map]
  rfl

theorem coreCode_encoded (s a b : Nat) (xs : List (Int × Int)) :
    (coreCode s a).eval (xs.map encodePoint,b)=
      (LatticeRouteCore.core s a b xs).map encodePoint := by
  rw [coreCode_eval,List.map_map]
  simp only [Function.comp_def,GridAssembly.Encoding.decode_encode]
  exact congrArg (fun l => (LatticeRouteCore.core s a b l).map encodePoint) (List.map_id xs)

def orientedCoreCode (s a : Nat) : Code OrientedInputTy CycleInputTy :=
  .comp (.pair (.comp (.pair .fst (.comp .snd .fst)) (orientCode PointTy)) (.comp .snd .snd))
    (coreCode s a)

theorem orientCode_decoded (xs : CycleInputTy.denote) (b : Bool) :
    ((orientCode PointTy).eval (xs,b)).map decoded=LatticeRouteDirections.orient (xs.map decoded) b := by
  rw [orientCode_eval]
  cases b <;> simp [LatticeRouteDirections.orient,List.map_reverse]

theorem orientedCoreCode_eval (s a b : Nat) (xs : CycleInputTy.denote) (rev : Bool) :
    (orientedCoreCode s a).eval (xs,rev,b)=
      (LatticeRouteCore.core s a b (LatticeRouteDirections.orient (xs.map decoded) rev)).map encodePoint := by
  change (coreCode s a).eval ((orientCode PointTy).eval (xs,rev),b)=_
  rw [coreCode_eval,orientCode_decoded]

theorem orientedCoreCode_encoded (s a b : Nat) (xs : List (Int × Int)) (rev : Bool) :
    (orientedCoreCode s a).eval (xs.map encodePoint,rev,b)=
      (LatticeRouteCore.core s a b (LatticeRouteDirections.orient xs rev)).map encodePoint := by
  rw [orientedCoreCode_eval,List.map_map]
  simp only [Function.comp_def,GridAssembly.Encoding.decode_encode]
  exact congrArg (fun l =>
    (LatticeRouteCore.core s a b (LatticeRouteDirections.orient l rev)).map encodePoint) (List.map_id xs)

/-- The actual corridor parameters: scale sixty-four and owner cut two. -/
def dockCoreCode : Code OrientedInputTy CycleInputTy := orientedCoreCode 64 2

theorem dockCoreCode_eval (xs : CycleInputTy.denote) (rev : Bool) (endCut : Nat) :
    dockCoreCode.eval (xs,rev,endCut)=
      (LatticeRouteCore.core 64 2 endCut (LatticeRouteDirections.orient (xs.map decoded) rev)).map encodePoint :=
  orientedCoreCode_eval 64 2 endCut xs rev

end GridHardness.LatticeRouteCoreCode
