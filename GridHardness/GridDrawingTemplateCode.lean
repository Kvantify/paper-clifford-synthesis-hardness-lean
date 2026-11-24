/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridFrameCode
public import GridHardness.GridAssemblyRectangles
public import GridHardness.SignedTentacleGraft

/-!
# Grid Drawing Template Code

Compile any fixed finite strip template to a certified program taking
its placement frame as input. The template is a program parameter, not an
unbounded run-time input; all variable coordinates are handled in binary.
-/

@[expose] public section

namespace GridHardness.GridDrawingTemplateCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridPointCode GridAssembly.Rectangles
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- A fixed rectangle with a variable outer placement. -/
def boxCode (g : Frame) (w h : Nat) : Code FrameTy RectangleTy :=
  .pair (.comp (.pair .id (.const FrameTy (encodeFrame g))) GridFrameCode.compose)
    (.const (.pair PaddingTy PaddingTy) (List.replicate w false,List.replicate h false))

theorem boxCode_eval (g : Frame) (w h : Nat) (f : FrameTy.denote) :
    (boxCode g w h).eval f = box ((decodeFrame f).comp g) w h := by
  change (GridFrameCode.compose.eval (f,encodeFrame g),_) = _
  rw [GridFrameCode.compose_eval,decode_encodeFrame]
  rfl

def drawingCode : Drawing → Code FrameTy GridPointCode.InputTy
  | .base g n => .comp (boxCode g (n+1) 2) .listSingle
  | .attach d g n => Code.append (drawingCode d) (.comp (boxCode g (n+1) 2) .listSingle)

theorem drawingCode_eval (d : Drawing) (f : FrameTy.denote) :
    (drawingCode d).eval f = drawing (decodeFrame f) d := by
  induction d with
  | base g n =>
    change [(boxCode g (n+1) 2).eval f] = _
    rw [boxCode_eval]
    rfl
  | attach d g n ih =>
    change (drawingCode d).eval f ++ [(boxCode g (n+1) 2).eval f] = _
    rw [ih,boxCode_eval]
    rfl

/-- Serialize only the strips added after the initial strip. -/
def tailRectangles (f : Frame) : Drawing → GridPointCode.InputTy.denote
  | .base _ _ => []
  | .attach d g n => tailRectangles f d ++ [box (f.comp g) (n+1) 2]

def tailCode : Drawing → Code FrameTy GridPointCode.InputTy
  | .base _ _ => .const GridPointCode.InputTy []
  | .attach d g n => Code.append (tailCode d) (.comp (boxCode g (n+1) 2) .listSingle)

theorem tailCode_eval (d : Drawing) (f : FrameTy.denote) :
    (tailCode d).eval f = tailRectangles (decodeFrame f) d := by
  induction d with
  | base g n => rfl
  | attach d g n ih =>
    change (tailCode d).eval f ++ [(boxCode g (n+1) 2).eval f] = _
    rw [ih,boxCode_eval]
    rfl

theorem tailRectangles_points (f : Frame) (d : Drawing) :
    GridPointCode.points (tailRectangles f d) = d.tailPoints.image f.map := by
  induction d with
  | base g n =>
    change GridPointCode.points [] = (∅ : Finset Point).image f.map
    rw [Finset.image_empty]
    exact GridAssembly.Rectangles.points_nil
  | attach d g n ih =>
    rw [tailRectangles,points_append,points_cons,points_nil,box_strip,
      GridAssembly.Rectangles.strip_comp,Finset.union_empty,ih,
      Drawing.tailPoints,Finset.image_union]

/-- Serialization commutes exactly with replacing a template's first strip. -/
theorem graft_rectangles (f : Frame) (old d : Drawing) :
    drawing f (Drawing.graft old d) = drawing f old ++ tailRectangles f d := by
  induction d with
  | base g n => simp [Drawing.graft,tailRectangles]
  | attach d g n ih => simp [Drawing.graft,drawing,tailRectangles,ih,List.append_assoc]

theorem drawingCode_points (d : Drawing) (f : FrameTy.denote) :
    GridPointCode.points ((drawingCode d).eval f) = d.points.image (decodeFrame f).map := by
  rw [drawingCode_eval,drawing_points]

theorem tailCode_points (d : Drawing) (f : FrameTy.denote) :
    GridPointCode.points ((tailCode d).eval f) = d.tailPoints.image (decodeFrame f).map := by
  rw [tailCode_eval,tailRectangles_points]

end GridHardness.GridDrawingTemplateCode
