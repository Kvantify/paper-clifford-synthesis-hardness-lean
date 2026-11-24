/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridPointCode
public import GridHardness.FrameComposition

/-!
# Grid Frame Code

Certified signed affine frame operations. Coordinates may be negative
or redundantly encoded; every produced frame has canonical signed coordinates.
These programs act on binary coordinates without enumerating their magnitudes.
-/

@[expose] public section

namespace GridHardness.GridFrameCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode GridPointCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Boolean exclusive-or, expressed in the certified program language. -/
def xor : Code (.pair .bool .bool) .bool :=
  .branch .fst (.branch .snd (.const .bool false) (.const .bool true)) .snd

@[simp] theorem xor_eval (a b : Bool) : xor.eval (a,b) = (a ^^ b) := by
  cases a <;> cases b <;> rfl

/-- Reflect a signed coordinate, also normalizing its representation. -/
def signed : Code (.pair .bool SignedTy) SignedTy :=
  .comp (.branch .fst (.comp .snd (.pair .snd .fst)) .snd) normalize

theorem signed_eval (b : Bool) (p : SignedTy.denote) :
    signed.eval (b,p) = encodeInt (sign b (integer p)) := by
  cases b
  · exact normalize_eval p
  · change normalize.eval (p.2,p.1) = _
    rw [normalize_eval]
    congr 1
    simp [integer, sign]

/-- Apply a signed orthogonal frame to an arbitrary signed point. -/
def point : Code (.pair FrameTy PointTy) PointTy :=
  let h : Code (.pair FrameTy PointTy) .bool := .comp .fst .fst
  let rx := .comp .fst (.comp .snd .fst)
  let ry := .comp .fst (.comp .snd (.comp .snd .fst))
  let origin : Code (.pair FrameTy PointTy) PointTy :=
    .comp .fst (.comp .snd (.comp .snd .snd))
  let u := .comp (.pair rx (.comp .snd .fst)) signed
  let v := .comp (.pair ry (.comp .snd .snd)) signed
  .pair (.comp (.pair (.comp origin .fst) (.branch h u v)) addSigned)
    (.comp (.pair (.comp origin .snd) (.branch h v u)) addSigned)

theorem point_eval (f : FrameTy.denote) (p : PointTy.denote) :
    point.eval (f,p) = encodePoint ((decodeFrame f).map (decoded p)) := by
  rcases f with ⟨h,rx,ry,x,y⟩
  rcases p with ⟨u,v⟩
  cases h <;>
    simp only [point, Code.eval, Bool.false_eq_true, ite_false, ite_true,
      decodeFrame, Frame.map, place, encodePoint, decoded]
  all_goals rw [addSigned_eval, addSigned_eval, signed_eval, signed_eval,
    integer_encodeInt, integer_encodeInt]

/-- Composition in application order: apply the second frame, then the first. -/
def compose : Code (.pair FrameTy FrameTy) FrameTy :=
  let fh : Code (.pair FrameTy FrameTy) .bool := .comp .fst .fst
  let fx := .comp .fst (.comp .snd .fst)
  let fy := .comp .fst (.comp .snd (.comp .snd .fst))
  let gh : Code (.pair FrameTy FrameTy) .bool := .comp .snd .fst
  let gx := .comp .snd (.comp .snd .fst)
  let gy := .comp .snd (.comp .snd (.comp .snd .fst))
  let go : Code (.pair FrameTy FrameTy) PointTy :=
    .comp .snd (.comp .snd (.comp .snd .snd))
  .pair (.branch fh gh (.branch gh (.const .bool false) (.const .bool true)))
    (.pair (.comp (.pair gx (.branch gh fx fy)) xor)
      (.pair (.comp (.pair gy (.branch gh fy fx)) xor)
        (.comp (.pair .fst go) point)))

theorem compose_eval (f g : FrameTy.denote) :
    compose.eval (f,g) = encodeFrame ((decodeFrame f).comp (decodeFrame g)) := by
  rcases f with ⟨fh,fx,fy,fo⟩
  rcases g with ⟨gh,gx,gy,go⟩
  cases fh <;> cases gh <;>
    simp only [compose, Code.eval, Bool.false_eq_true, ite_false, ite_true,
      encodeFrame, decodeFrame, Frame.comp]
  all_goals rw [xor_eval, xor_eval, point_eval]
  all_goals rfl

/-- Transport one rectangle while retaining its explicit width and height. -/
def rectangle : Code (.pair FrameTy RectangleTy) RectangleTy :=
  .pair (.comp (.pair .fst (.comp .snd .fst)) compose) (.comp .snd .snd)

theorem rectangle_eval (f : FrameTy.denote) (r : RectangleTy.denote) :
    rectangle.eval (f,r) =
      (encodeFrame ((decodeFrame f).comp (decodeFrame r.1)),r.2) := by
  change (compose.eval (f,r.1),r.2) = _
  rw [compose_eval]

/-- Transport an entire rectangle description with shared frame input. -/
def rectangles : Code (.pair FrameTy GridPointCode.InputTy) GridPointCode.InputTy := .listMapEnv rectangle

theorem rectangles_eval (f : FrameTy.denote) (rs : GridPointCode.InputTy.denote) :
    rectangles.eval (f,rs) =
      rs.map (fun r => (encodeFrame ((decodeFrame f).comp (decodeFrame r.1)),r.2)) := by
  change rs.map (fun r => rectangle.eval (f,r)) = _
  apply List.map_congr_left
  intro r _
  exact rectangle_eval f r

end GridHardness.GridFrameCode
