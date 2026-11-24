/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBodyVertexCode

/-!
# SAT Exterior Route Code

The six exterior path templates as SAT-fed bounded-list programs.
Only the appropriate four or five templates will be emitted by the record
compiler; this file supplies exact point and route computations.
-/

@[expose] public section

namespace GridHardness.SatExteriorRouteCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1200000

abbrev InputTy := Ty.pair SatTy .nat

def affine (a b : Nat) : Code InputTy .nat :=
  Code.add (Code.mul (.const .nat a) (.comp .fst .listLen)) (.const .nat b)

def signed (a b : Code InputTy .nat) : Code InputTy SignedTy := .comp (.pair a b) normalize
def positive (a : Code InputTy .nat) : Code InputTy SignedTy := signed a (.const .nat 0)

theorem affine_eval (a b : Nat) (x : SatTy.denote) (k : Nat) :
    (affine a b).eval (x,k)=a*x.length+b := rfl
theorem signed_eval (a b : Code InputTy .nat) (z : InputTy.denote) :
    (signed a b).eval z=encodeInt ((a.eval z:Int)-b.eval z) := normalize_eval _

def bottomPoint : Code InputTy PointTy :=
  .pair (signed .snd (.const .nat 128)) (.const SignedTy (encodeInt (-64)))
def firstPoint : Code InputTy PointTy :=
  .pair (positive (affine 1536 641)) (signed .snd (.const .nat 64))
def forwardPoint : Code InputTy PointTy :=
  .branch (.comp (.pair .snd (.const .nat 64)) .natLe)
    (.pair (positive (Code.add (affine 1536 641) .snd)) (positive (affine 1536 192)))
    (.branch (.comp (.pair .snd (affine 1536 512)) .natLe)
      (.pair (positive (affine 1536 705)) (positive (Code.add (affine 1536 128) .snd)))
      (.branch (.comp (.pair .snd (affine 3072 1281)) .natLe)
        (.pair (signed (affine 3072 1217) .snd) (positive (affine 3072 640)))
        (.pair (.const SignedTy (encodeInt (-64))) (signed (affine 6144 1921) .snd))))
def returnPoint : Code InputTy PointTy :=
  .branch (.comp (.pair .snd (affine 1536 1020)) .natLe)
    (.pair (.const SignedTy (encodeInt (-64))) (signed (affine 1536 1020) .snd))
    (.pair (signed (affine 1536 956) .snd) (.const SignedTy (encodeInt 0)))

theorem bottomPoint_eval (x : SatTy.denote) (k : Nat) :
    bottomPoint.eval (x,k)=encodePoint (SatExteriorLattice.bottomPoint k) := by
  simp only [bottomPoint,signed,Code.eval,normalize_eval,integer,encodePoint,
    SatExteriorLattice.bottomPoint]
  congr 2 <;> ring

theorem firstPoint_eval (x : SatTy.denote) (k : Nat) :
    firstPoint.eval (x,k)=encodePoint
      (SatVariableLattice.wireX (3*x.length)+64,-64+(k:Int)) := by
  simp only [firstPoint,positive,signed,affine,Code.add,Code.mul,Code.eval,
    normalize_eval,integer,encodePoint,SatVariableLattice.wireX,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.sub_zero]
  congr 2 <;> ring

theorem forwardPoint_eval (x : SatTy.denote) (k : Nat) :
    forwardPoint.eval (x,k)=encodePoint (SatExteriorLattice.forwardPoint (3*x.length) k) := by
  have h₁ : 512*(3*x.length)+512=1536*x.length+512 := by omega
  have h₂ : 1024*(3*x.length)+1281=3072*x.length+1281 := by omega
  simp only [forwardPoint,positive,signed,affine,Code.add,Code.mul,Code.eval,
    normalize_eval,integer,decide_eq_true_eq,SatExteriorLattice.forwardPoint,h₁,h₂]
  split_ifs <;>
    simp only [encodePoint,SatVariableLattice.wireX,SatExteriorLattice.top,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.sub_zero]
  all_goals congr 2 <;> ring

theorem returnPoint_eval (x : SatTy.denote) (k : Nat) :
    returnPoint.eval (x,k)=encodePoint (SatExteriorLattice.returnPoint (3*x.length) k) := by
  have h : 512*(3*x.length)+1020=1536*x.length+1020 := by omega
  simp only [returnPoint,signed,affine,Code.add,Code.mul,Code.eval,
    normalize_eval,integer,decide_eq_true_eq,SatExteriorLattice.returnPoint,h]
  split_ifs <;> simp only [encodePoint,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  all_goals congr 2 <;> ring

def mapRange (a b : Nat) (f : Code InputTy PointTy) : Code SatTy CycleInputTy :=
  .comp (.pair .id (SatAffineRangeCode.code a b)) (.listMapEnv f)

theorem mapRange_eval (a b : Nat) (f : Code InputTy PointTy) (x : SatTy.denote) :
    (mapRange a b f).eval x=(List.range (a*x.length+b)).map (fun k => f.eval (x,k)) := by
  change ((SatAffineRangeCode.code a b).eval x).map _=_
  rw [SatAffineRangeCode.code_eval]
  rfl

def route : Fin 6 → Code SatTy CycleInputTy
  | 0 => .const CycleInputTy (SatExteriorLattice.down.map encodePoint)
  | 1 => mapRange 1536 770 bottomPoint
  | 2 => mapRange 0 193 firstPoint
  | 3 => mapRange 3072 1406 forwardPoint
  | 4 => mapRange 1536 1085 returnPoint
  | 5 => .const CycleInputTy (SatExteriorLattice.closing.map encodePoint)

def tag {m : Nat} : SatExteriorDrawing.Edge m → Fin 6
  | .sentinelFirst => 0
  | .sentinelSecond => 1
  | .firstVariable => 2
  | .forward _ => 3
  | .returning _ => 4
  | .closing _ => 5

theorem route_eval (x : SatTy.denote) (e : SatExteriorDrawing.Edge x.length) :
    (route (tag e)).eval x=(SatExteriorDrawing.route x e).map encodePoint := by
  cases e with
  | sentinelFirst => rfl
  | sentinelSecond =>
    simp only [tag,route,mapRange_eval,bottomPoint_eval x,SatExteriorDrawing.route,SatExteriorLattice.bottom,
      List.map_map,Function.comp_def]
    apply congrArg (List.map _)
    apply congrArg List.range
    omega
  | firstVariable =>
    simp only [tag,route,mapRange_eval,firstPoint_eval x,Nat.zero_mul,Nat.zero_add,
      SatExteriorDrawing.route,SatExteriorLattice.firstVariable,SatCrossingRouting.rising,List.map_map,
      Function.comp_def]
  | forward h =>
    simp only [tag,route,mapRange_eval,forwardPoint_eval x,SatExteriorDrawing.route,SatExteriorLattice.forward,
      List.map_map,Function.comp_def]
    apply congrArg (List.map _)
    apply congrArg List.range
    omega
  | returning h =>
    simp only [tag,route,mapRange_eval,returnPoint_eval x,SatExteriorDrawing.route,SatExteriorLattice.returning,
      List.map_map,Function.comp_def]
    apply congrArg (List.map _)
    apply congrArg List.range
    omega
  | closing h => rfl

end GridHardness.SatExteriorRouteCode
