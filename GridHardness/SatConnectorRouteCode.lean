/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatHorizontalDrawing
public import GridHardness.SatVerticalArcs
public import GridHardness.LatticeInterpolationCode
public import GridHardness.LatticeRouteOrientationCode

/-!
# SAT Connector Route Code

Pointwise arithmetic for the intercell routes. The variable-length loops
are supplied with explicitly bounded index lists by the SAT-fed compilers.
-/

@[expose] public section

namespace GridHardness.SatConnectorRouteCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open LatticeRouteCoreCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev BendTy := Ty.pair PointTy .nat
abbrev SampleTy := Ty.pair BendTy .nat

def natSigned {τ : Ty} (c : Code τ .nat) : Code τ SignedTy :=
  .comp (.pair c (.const .nat 0)) normalize

theorem natSigned_eval {τ : Ty} (c : Code τ .nat) (x : τ.denote) :
    (natSigned c).eval x=encodeInt (c.eval x) := by
  change normalize.eval (c.eval x,0)=_
  rw [normalize_eval]
  congr 1

def plus {τ : Ty} (a b : Code τ SignedTy) : Code τ SignedTy := .comp (.pair a b) addSigned
def minus {τ : Ty} (a b : Code τ SignedTy) : Code τ SignedTy := .comp (.pair a b) subSigned

theorem plus_eval {τ : Ty} (a b : Code τ SignedTy) (x : τ.denote) :
    (plus a b).eval x=encodeInt (integer (a.eval x)+integer (b.eval x)) := addSigned_eval _ _
theorem minus_eval {τ : Ty} (a b : Code τ SignedTy) (x : τ.denote) :
    (minus a b).eval x=encodeInt (integer (a.eval x)-integer (b.eval x)) := subSigned_eval _ _

/-- The three pieces of the horizontal upper bend, including its endpoints. -/
def bendPoint : Code SampleTy PointTy :=
  let a : Code SampleTy SignedTy := .comp .fst (.comp .fst .fst)
  let y : Code SampleTy SignedTy := .comp .fst (.comp .fst .snd)
  let len : Code SampleTy .nat := .comp .fst .snd
  let k : Code SampleTy .nat := .snd
  .branch (.comp (.pair k len) .natLe)
    (.pair (plus a (natSigned k)) (plus y (.const SignedTy (encodeInt 10))))
    (.branch (.comp (.pair k (Code.add len (.const .nat 6))) .natLe)
      (.pair (plus a (natSigned len))
        (minus (plus (plus y (.const SignedTy (encodeInt 10))) (natSigned len)) (natSigned k)))
      (.pair (minus (plus a (natSigned k)) (.const SignedTy (encodeInt 6)))
        (plus y (.const SignedTy (encodeInt 4)))))

theorem bendPoint_eval (a y : Int) (len k : Nat) :
    bendPoint.eval ((encodePoint (a,y),len),k)=
      encodePoint (SatCrossingHorizontal.bendPoint a y len k) := by
  by_cases h : k≤len <;> by_cases hh : k≤len+6
  all_goals
    simp [bendPoint,Code.add,Code.eval,plus_eval,minus_eval,natSigned_eval,
      encodePoint,integer_encodeInt,SatCrossingHorizontal.bendPoint,h,hh]
    <;> congr 1 <;> omega

/-- Reflection of a sampled upper point about its horizontal centreline. -/
def reflectedPoint : Code SampleTy PointTy :=
  .pair (.comp bendPoint .fst)
    (minus (plus (.comp .fst (.comp .fst .snd)) (.comp .fst (.comp .fst .snd)))
      (.comp bendPoint .snd))

theorem reflectedPoint_eval (a y : Int) (len k : Nat) :
    reflectedPoint.eval ((encodePoint (a,y),len),k)=
      encodePoint ((SatCrossingHorizontal.reflection y).map
        (SatCrossingHorizontal.bendPoint a y len k)) := by
  change ((bendPoint.eval ((encodePoint (a,y),len),k)).1,
    subSigned.eval (addSigned.eval (encodeInt y,encodeInt y),
      (bendPoint.eval ((encodePoint (a,y),len),k)).2))=_
  rw [bendPoint_eval,addSigned_eval,subSigned_eval]
  simp only [encodePoint,integer_encodeInt,SatCrossingHorizontal.reflection_map,two_mul]

/-- One point of an inclusive vertical run. -/
def risingPoint : Code (.pair PointTy .nat) PointTy :=
  .pair (.comp .fst (.comp .fst normalize))
    (plus (.comp .fst .snd) (natSigned .snd))

theorem risingPoint_eval (a y : Int) (k : Nat) :
    risingPoint.eval (encodePoint (a,y),k)=encodePoint (a,y+(k:Int)) := by
  change (normalize.eval (encodeInt a),addSigned.eval (encodeInt y,(natSigned (.snd : Code (.pair PointTy .nat) .nat)).eval (encodePoint (a,y),k)))=_
  rw [normalize_eval,natSigned_eval,addSigned_eval]
  simp only [integer_encodeInt,Code.eval,encodePoint]

/-- Mapping over the actual index range reproduces the geometric definitions. -/
theorem upper_map (a y : Int) (len : Nat) :
    (List.range (len+17)).map (fun k => bendPoint.eval ((encodePoint (a,y),len),k))=
      (SatCrossingHorizontal.upperPath a y len).map encodePoint := by
  simp only [SatCrossingHorizontal.upperPath,List.map_map]
  exact List.map_congr_left (fun k _ => bendPoint_eval a y len k)

theorem lower_map (a y : Int) (len : Nat) :
    ((List.range (len+17)).map (fun k => reflectedPoint.eval ((encodePoint (a,y),len),k))).reverse=
      (SatCrossingHorizontal.lowerPath a y len).map encodePoint := by
  simp only [SatCrossingHorizontal.lowerPath,SatCrossingHorizontal.upperPath,
    List.map_reverse,List.map_map]
  congr 1
  exact List.map_congr_left (fun k _ => reflectedPoint_eval a y len k)

theorem rising_map (a y : Int) (h : Nat) :
    (List.range (h+1)).map (fun k => risingPoint.eval (encodePoint (a,y),k))=
      (SatCrossingRouting.rising a y h).map encodePoint := by
  simp only [SatCrossingRouting.rising,List.map_map]
  exact List.map_congr_left (fun k _ => risingPoint_eval a y k)

/-- A sampled path with a fixed orientation; no binary-size loop is introduced. -/
def path (f : Code SampleTy PointTy) (rev : Bool) :
    Code (.pair BendTy (.list .nat)) CycleInputTy :=
  .comp (.listMapEnv f) (if rev then LatticeRouteCoreCode.reverseCode PointTy else .id)

theorem path_eval (f : Code SampleTy PointTy) (rev : Bool)
    (z : BendTy.denote) (ks : List Nat) :
    (path f rev).eval (z,ks)=
      if rev then (ks.map (fun k => f.eval (z,k))).reverse else ks.map (fun k => f.eval (z,k)) := by
  cases rev
  · rfl
  · change (LatticeRouteCoreCode.reverseCode PointTy).eval _ = _
    exact LatticeRouteCoreCode.reverseCode_eval (τ:=PointTy) _

end GridHardness.SatConnectorRouteCode
