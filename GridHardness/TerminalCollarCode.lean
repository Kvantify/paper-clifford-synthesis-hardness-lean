/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridDrawingTemplateCode
public import GridHardness.TerminalCollarMatch

/-!
# Terminal Collar Code

Certified selection, placement, and grafting of the eight fixed receiving
collars. The natural side field uses 0,1,2,3 for the four sides; every other
value selects side 3, so the programs are total even on malformed input.
-/

@[expose] public section

namespace GridHardness.TerminalCollarCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridPointCode GridAssembly.Rectangles
open GridDrawingTemplateCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev InputTy := Ty.pair .nat (.pair .bool FrameTy)

/-- Compile a four-way fixed family, each member having two lane phases. -/
def select (family : Fin 4 → Bool → Code FrameTy GridPointCode.InputTy) :
    Code InputTy GridPointCode.InputTy :=
  let sideTest (side : Nat) : Code InputTy .bool :=
    .comp (.pair .fst (.const .nat side)) .natEq
  let chooseSide (s : Fin 4) : Code InputTy GridPointCode.InputTy :=
    .branch (.comp .snd .fst)
      (.comp (.comp .snd .snd) (family s true))
      (.comp (.comp .snd .snd) (family s false))
  .branch (sideTest 0) (chooseSide 0)
    (.branch (sideTest 1) (chooseSide 1) (.branch (sideTest 2) (chooseSide 2) (chooseSide 3)))

theorem select_eval (family : Fin 4 → Bool → Code FrameTy GridPointCode.InputTy)
    (s : Fin 4) (b : Bool) (f : FrameTy.denote) :
    (select family).eval (s.val,b,f) = (family s b).eval f := by
  fin_cases s <;> cases b <;> rfl

/-- The full five-strip receiving collar. -/
def full : Code InputTy GridPointCode.InputTy :=
  select (fun s b => drawingCode (TerminalCollarMatched.phaseDrawing s b))

/-- Only the four strips appended when the existing route replaces its entry strip. -/
def tail : Code InputTy GridPointCode.InputTy :=
  select (fun s b => tailCode (TerminalCollarMatched.phaseDrawing s b))

theorem full_eval (s : Fin 4) (b : Bool) (f : FrameTy.denote) :
    full.eval (s.val,b,f) = drawing (decodeFrame f) (TerminalCollarMatched.phaseDrawing s b) := by
  rw [full,select_eval,drawingCode_eval]

theorem tail_eval (s : Fin 4) (b : Bool) (f : FrameTy.denote) :
    tail.eval (s.val,b,f) =
      tailRectangles (decodeFrame f) (TerminalCollarMatched.phaseDrawing s b) := by
  rw [tail,select_eval,tailCode_eval]

theorem full_points (s : Fin 4) (b : Bool) (f : FrameTy.denote) :
    GridPointCode.points (full.eval (s.val,b,f)) =
      (TerminalCollarMatched.phaseDrawing s b).points.image (decodeFrame f).map := by
  rw [full_eval,drawing_points]

theorem tail_points (s : Fin 4) (b : Bool) (f : FrameTy.denote) :
    GridPointCode.points (tail.eval (s.val,b,f)) =
      (TerminalCollarMatched.tail s b).image (decodeFrame f).map := by
  rw [tail_eval,tailRectangles_points]
  rfl

/-- Append the finite tail to a rectangle description of the earlier route. -/
def graft : Code (.pair InputTy GridPointCode.InputTy) GridPointCode.InputTy :=
  Code.append .snd (.comp .fst tail)

theorem graft_eval (s : Fin 4) (b : Bool) (f : FrameTy.denote) (old : Drawing) :
    graft.eval ((s.val,b,f),drawing (decodeFrame f) old) =
      drawing (decodeFrame f) (TerminalCollarMatched.attach old s b) := by
  change drawing (decodeFrame f) old ++ tail.eval (s.val,b,f) = _
  rw [tail_eval,← graft_rectangles]
  rfl

/-- Exact set semantics also applies to any rectangle encoding of the old route. -/
theorem graft_points (s : Fin 4) (b : Bool) (f : FrameTy.denote)
    (rs : GridPointCode.InputTy.denote) :
    GridPointCode.points (graft.eval ((s.val,b,f),rs)) =
      GridPointCode.points rs ∪ (TerminalCollarMatched.tail s b).image (decodeFrame f).map := by
  change GridPointCode.points (rs ++ tail.eval (s.val,b,f)) = _
  rw [points_append,tail_points]

/-- Select the transverse phase from the final strip, side, and tracked lane.
The Boolean lane is false for lane zero and true for lane one. -/
def phase : Code (.pair FrameTy (.pair .nat .bool)) .bool :=
  let ry : Code (.pair FrameTy (.pair .nat .bool)) .bool :=
    .comp .fst (.comp .snd (.comp .snd .fst))
  let side : Code (.pair FrameTy (.pair .nat .bool)) .nat := .comp .snd .fst
  let flip : Code (.pair FrameTy (.pair .nat .bool)) .bool :=
    .branch (.comp (.pair side (.const .nat 1)) .natEq) (.const .bool true)
      (.comp (.pair side (.const .nat 2)) .natEq)
  .comp (.pair (.comp (.pair (.comp .snd .snd) ry) GridFrameCode.xor) flip) GridFrameCode.xor

theorem phase_eval (f : FrameTy.denote) (s : Fin 4) (lane : Fin 2) :
    phase.eval (f,s.val,decide (lane=1)) = TerminalCollarMatch.phaseFor (decodeFrame f) s lane := by
  rcases f with ⟨h,rx,ry,o⟩
  fin_cases s <;> fin_cases lane <;> cases ry <;> rfl

end GridHardness.TerminalCollarCode
