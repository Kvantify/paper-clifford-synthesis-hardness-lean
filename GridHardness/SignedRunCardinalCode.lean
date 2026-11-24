/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedRunCardinalFormula
public import GridHardness.GridFrameCode
public import GridHardness.LatticeRouteCodeLists
public import GridHardness.LatticeRouteRunScan

/-!
# Signed Run Cardinal Code

Bounded-list programs evaluating the local and prefix formulas for
cardinal strip chains. Integer origins are binary encoded, while rectangle
side lengths are materialized only from an explicit padding reservoir.
-/

@[expose] public section

namespace GridHardness.SignedRunCardinalCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems.GridCode GridPointCode SignedRunCode
open SignedRunCardinalFormula LatticeRouteRunsCode LatticeRouteCodeLists
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev RunTy := Ty.pair .nat .nat
abbrev RunsTy := Ty.list RunTy
abbrev RegularTy := Ty.pair PointTy (.pair .nat (.pair .bool .bool))

/-- The sign of a cardinal direction; validity is needed only for the
geometric interpretation of the input direction. -/
def negativeCode : Code .nat .bool := .comp (.pair (.const .nat 2) .id) .natLe

@[simp] theorem negativeCode_eval (d : Fin 4) :
    negativeCode.eval d.val = negative d := rfl

def horizontalCode : Code .nat .bool :=
  .comp (.pair (.comp (.pair .id (.const .nat 0)) .natEq)
    (.comp (.pair .id (.const .nat 2)) .natEq)) .boolOr

theorem horizontalCode_eval (d : Fin 4) :
    horizontalCode.eval d.val = decide (d.val%2=0) := by fin_cases d <;> rfl

/-- Recover a Boolean at a bounded input-list position, defaulting to false. -/
def boolAt : Code (.pair (.list .bool) .nat) .bool :=
  .comp (.pair (.comp (.comp Code.listNth (.listMap bitNat)) .listSum)
    (.const .nat 1)) .natEq

theorem boolAt_eval (bs : List Bool) (i : Nat) :
    boolAt.eval (bs,i) = bs[i]?.getD false := by
  change decide ((((Code.listNth (τ:=.bool)).eval (bs,i)).map bitNat.eval).sum=1)=_
  rw [listNth_option]
  cases h : bs[i]? with
  | none => rfl
  | some b => cases b <;> rfl

/-- Produce a phase-corrected state directly from the ideal start, cardinal
direction, preceding sign and sign two positions back. -/
def regularCode : Code RegularTy StateTy :=
  let d : Code RegularTy .nat := .comp .snd .fst
  let h := .comp d horizontalCode
  let rx := .comp d negativeCode
  let previous : Code RegularTy .bool := .comp .snd (.comp .snd .fst)
  let older : Code RegularTy .bool := .comp .snd (.comp .snd .snd)
  let phase := .comp (.pair rx older) GridFrameCode.xor
  let basis : Code RegularTy FrameTy :=
    .pair h (.pair rx (.pair (.const .bool false) .fst))
  let offset : Code RegularTy PointTy :=
    .pair (.branch phase (.const SignedTy (0,1)) (.const SignedTy (0,0)))
      (.const SignedTy (0,0))
  .pair (.pair h (.pair rx (.pair previous
    (.comp (.pair basis offset) GridFrameCode.point))))
    (.pair phase (.const .bool false))

theorem regularCode_eval (p : Point) (d : Fin 4) (previous older : Bool) :
    regularCode.eval (encodePoint p,d.val,previous,older) =
      encodeState (regular p d previous older) := by
  fin_cases d <;> cases previous <;> cases older <;>
    simp only [regularCode, Code.eval, horizontalCode, negativeCode, GridFrameCode.xor,
      encodeState, regular, negative, encodeBit, bit, encodeFrame, frameAlong]
  all_goals
    simp
    rw [GridFrameCode.point_eval]
    simp only [decodeFrame, GridAssembly.Encoding.decode_encode]
    simp [decoded, integer, Frame.map, place, sign]

/-- Sum the lengths of runs having one selected cardinal direction. -/
def total (d : Nat) : Code RunsTy .nat :=
  .comp (.listFilter (.comp (.pair .fst (.const .nat d)) .natEq))
    (.comp (.listMap .snd) .listSum)

def directionTotal (rs : List Run) (d : Nat) : Nat :=
  ((rs.filter (fun r => decide (r.1.val=d))).map Prod.snd).sum

theorem total_eval (d : Nat) (rs : List Run) :
    (total d).eval (rs.map encodeRun) = directionTotal rs d := by
  simp [total, Code.eval, directionTotal, List.filter_map, List.map_map,
    encodeRun, Function.comp_def]
  rfl

theorem displacement_totals (rs : List Run) : displacement rs =
    ((directionTotal rs 0 : Int)-directionTotal rs 2,
      (directionTotal rs 1 : Int)-directionTotal rs 3) := by
  induction rs with
  | nil => simp [displacement, directionTotal]
  | cons r rs ih =>
    rcases r with ⟨d,n⟩
    have hx := congrArg Prod.fst ih
    have hy := congrArg Prod.snd ih
    fin_cases d <;>
      simp [displacement, directionTotal, DirectedLocalLayout.ray] at hx hy ⊢ <;>
      omega

/-- Exact binary-coordinate evaluation of the signed displacement sum. -/
def translateCode : Code (.pair PointTy RunsTy) PointTy :=
  .pair (.comp (.pair (.comp .fst .fst)
    (.pair (.comp .snd (total 0)) (.comp .snd (total 2)))) addSigned)
    (.comp (.pair (.comp .fst .snd)
      (.pair (.comp .snd (total 1)) (.comp .snd (total 3)))) addSigned)

theorem translateCode_eval (p : Point) (rs : List Run) :
    translateCode.eval (encodePoint p,rs.map encodeRun) = encodePoint (translate p rs) := by
  simp only [translateCode, Code.eval]
  rw [addSigned_eval, addSigned_eval, total_eval, total_eval, total_eval, total_eval]
  change (encodeInt (integer (encodeInt p.1) + integer (directionTotal rs 0,directionTotal rs 2)),
    encodeInt (integer (encodeInt p.2) + integer (directionTotal rs 1,directionTotal rs 3))) = _
  rw [integer_encodeInt, integer_encodeInt]
  rw [translate, displacement_totals]
  rfl

/-- Unary padding for a binary length is cut from a supplied explicit list.
The program has no numeric-range enumeration. -/
def padding : Code (.pair PaddingTy .nat) PaddingTy :=
  .comp (takeCode .bool) (.listMap (.const .bool false))

theorem padding_eval (pad : List Bool) (n : Nat) (hn : n ≤ pad.length) :
    padding.eval (pad,n) = List.replicate n false := by
  change ((takeCode .bool).eval (pad,n)).map (fun _ => false)=_
  rw [takeCode_eval]
  simpa only [List.length_take, Nat.min_eq_left hn] using
    (List.map_const' (l:=pad.take n) (b:=false))

end GridHardness.SignedRunCardinalCode
