/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TerminalCollarCode
public import GridHardness.TerminalCollarAttach
public import GridHardness.SignedTentacleInverse

/-!
# Terminal Collar Attach Code

The actual receiving operation as a certified rectangle program: infer
its lane phase from the final strip, place the fixed collar at the recipient
anchor, and append its four new strips. No localization of the old rectangle
list is needed.
-/

@[expose] public section

namespace GridHardness.TerminalCollarAttachCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode GridPointCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Canonically encoded translation by an arbitrary signed point. -/
def shift : Code PointTy FrameTy :=
  .pair (.const .bool true) (.pair (.const .bool false) (.pair (.const .bool false)
    (.pair (.comp .fst normalize) (.comp .snd normalize))))

theorem shift_eval (p : PointTy.denote) :
    shift.eval p = encodeFrame (TerminalCollarAttach.shift (decoded p)) := by
  change (true,false,false,(normalize.eval p.1,normalize.eval p.2)) = _
  rw [normalize_eval,normalize_eval]
  rfl

/-- Translating the old drawing does not change the selected transverse phase. -/
theorem phase_translation (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2) :
    TerminalCollarAttach.phase a old s lane = TerminalCollarMatch.phaseFor old.lastFrame s lane := by
  unfold TerminalCollarAttach.phase TerminalCollarMatch.chosenPhase
  rw [TerminalCollarAttach.localize_lastFrame]
  unfold TerminalCollarMatch.phaseFor
  have hy : ((TerminalCollarAttach.unshift a).comp old.lastFrame).reverseY =
      old.lastFrame.reverseY := by
    rcases old.lastFrame with ⟨h,x,y,o⟩
    cases h <;> cases y <;> rfl
  rw [hy]

abbrev RequestTy := Ty.pair PointTy (.pair FrameTy (.pair .nat .bool))

/-- All information needed for the finite receiving tail. -/
def request : Code RequestTy TerminalCollarCode.InputTy :=
  .pair (.comp .snd (.comp .snd .fst))
    (.pair (.comp .snd TerminalCollarCode.phase) (.comp .fst shift))

theorem request_eval (a : PointTy.denote) (old : Drawing) (s : Fin 4) (lane : Fin 2) :
    request.eval (a,encodeFrame old.lastFrame,s.val,decide (lane=1)) =
      (s.val,TerminalCollarAttach.phase (decoded a) old s lane,
        encodeFrame (TerminalCollarAttach.shift (decoded a))) := by
  change (s.val,TerminalCollarCode.phase.eval (encodeFrame old.lastFrame,s.val,decide (lane=1)),
    shift.eval a) = _
  rw [TerminalCollarCode.phase_eval,decode_encodeFrame,shift_eval,phase_translation]

def tail : Code RequestTy GridPointCode.InputTy := .comp request TerminalCollarCode.tail

theorem tail_eval (a : PointTy.denote) (old : Drawing) (s : Fin 4) (lane : Fin 2) :
    tail.eval (a,encodeFrame old.lastFrame,s.val,decide (lane=1)) =
      GridDrawingTemplateCode.tailRectangles (TerminalCollarAttach.shift (decoded a))
        (TerminalCollarMatched.phaseDrawing s (TerminalCollarAttach.phase (decoded a) old s lane)) := by
  change TerminalCollarCode.tail.eval (request.eval _) = _
  rw [request_eval,TerminalCollarCode.tail_eval,decode_encodeFrame]

def attach : Code (.pair RequestTy GridPointCode.InputTy) GridPointCode.InputTy :=
  Code.append .snd (.comp .fst tail)

theorem attach_points (a : PointTy.denote) (old : Drawing) (s : Fin 4) (lane : Fin 2)
    (rs : GridPointCode.InputTy.denote) (hrs : GridPointCode.points rs =old.points) :
    GridPointCode.points (attach.eval ((a,encodeFrame old.lastFrame,s.val,decide (lane=1)),rs)) =
      (TerminalCollarAttach.attach (decoded a) old s lane).points := by
  change GridPointCode.points (rs ++ tail.eval
    (a,encodeFrame old.lastFrame,s.val,decide (lane=1))) = _
  rw [GridAssembly.Rectangles.points_append,hrs,tail_eval,
    GridDrawingTemplateCode.tailRectangles_points,TerminalCollarAttach.attach_eq_graft,
    Drawing.graft_points]
  congr 1
  exact (Drawing.transform_tailPoints _ _).symm

end GridHardness.TerminalCollarAttachCode
