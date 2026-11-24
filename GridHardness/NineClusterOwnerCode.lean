/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridFrameCode
public import GridHardness.SignedRunCode
public import GridHardness.NineClusterOwnerRun

/-!
# Nine Cluster Owner Code

Certified initialization of the signed route compiler at an owner's
prescribed two-edge cluster dock. The tracked ideal centerline is lane one;
the initial phase is zero, exactly as in the semantic SAT construction.
-/

@[expose] public section

namespace GridHardness.NineClusterOwnerCode
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridPointCode SignedRunCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Select a canonical owner dock, with side 3 as the total default. -/
def dock : Code .nat FrameTy :=
  let test (i : Nat) : Code .nat .bool := .comp (.pair .id (.const .nat i)) .natEq
  .branch (test 0) (.const FrameTy (encodeFrame (NineClusterAttachment.dock true 0)))
    (.branch (test 1) (.const FrameTy (encodeFrame (NineClusterAttachment.dock true 1)))
      (.branch (test 2) (.const FrameTy (encodeFrame (NineClusterAttachment.dock true 2)))
        (.const FrameTy (encodeFrame (NineClusterAttachment.dock true 3)))))

theorem dock_eval (s : Fin 4) :
    dock.eval s.val = encodeFrame (NineClusterAttachment.dock true s) := by
  fin_cases s <;> rfl

/-- Place the dock in the cluster's frame and initialize phase and lane. -/
def state : Code (.pair FrameTy .nat) StateTy :=
  .pair (.comp (.pair .fst (.comp .snd dock)) GridFrameCode.compose)
    (.const (.pair .bool .bool) (false,true))

theorem state_eval (f : FrameTy.denote) (s : Fin 4) :
    state.eval (f,s.val) = encodeState (NineClusterOwnerRun.state (decodeFrame f) s) := by
  change (GridFrameCode.compose.eval (f,dock.eval s.val),false,true) = _
  rw [dock_eval,GridFrameCode.compose_eval,decode_encodeFrame]
  rfl

/-- The first strip takes its length from an explicit list. -/
def firstRectangle : Code (.pair (.pair FrameTy .nat) PaddingTy) RectangleTy :=
  .comp (.pair (.comp .fst state) .snd) SignedRunCode.rectangle

theorem firstRectangle_eval (f : FrameTy.denote) (s : Fin 4) (n : Nat) :
    firstRectangle.eval ((f,s.val),List.replicate n false) =
      GridAssembly.Rectangles.box ((decodeFrame f).comp (NineClusterAttachment.dock true s))
        (n+1) 2 := by
  change SignedRunCode.rectangle.eval (state.eval (f,s.val),List.replicate n false) = _
  rw [state_eval,SignedRunCode.rectangle_eval,NineClusterOwnerRun.state_length]
  rfl

end GridHardness.NineClusterOwnerCode
