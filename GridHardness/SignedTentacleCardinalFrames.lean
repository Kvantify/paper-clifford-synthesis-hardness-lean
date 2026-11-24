/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleRunGeometry
public import GridHardness.LatticeRouteRuns

/-!
# Signed Tentacle Cardinal Frames

Executable cardinal-direction control of signed strip frames. A
perpendicular desired direction determines the signed turn bit, including
the transverse reflection of the current frame.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The direction of increasing longitudinal coordinates. -/
def Frame.axisDirection (f : Frame) : Fin 4 :=
  if f.horizontal then (if f.reverseX then 2 else 0)
  else (if f.reverseX then 3 else 1)

/-- The signed turn which realizes the requested perpendicular direction.
Its sign is relative to the current transverse axis, not to the plane. -/
def Frame.chooseTurn (f : Frame) (d : Fin 4) : Bool :=
  decide (2 ≤ d.val) ^^ f.reverseY

theorem Frame.axis_advance (f : Frame) (x y : Int) (n : Nat) :
    f.map (x + n, y) =
      LatticeRouteRuns.advance (f.map (x, y)) f.axisDirection n := by
  rcases f with ⟨h, rx, ry, p⟩
  cases h <;> cases rx <;> cases ry <;>
    simp [Frame.map, Frame.axisDirection, place, sign,
      LatticeRouteRuns.advance, DirectedLocalLayout.ray] <;> omega

/-- Both possible perpendicular directions are realized by the explicit
choice of turn bit. No direction selection is assumed. -/
theorem Frame.next_axisDirection (f : Frame) (a : Nat) (d : Fin 4)
    (hd : f.axisDirection.val % 2 ≠ d.val % 2) :
    (nextFrame f a (f.chooseTurn d)).axisDirection = d := by
  rcases f with ⟨h, rx, ry, p⟩
  cases h <;> cases rx <;> cases ry <;> fin_cases d <;>
    simp [Frame.axisDirection, Frame.chooseTurn, nextFrame, Frame.comp,
      turnFrame] at hd ⊢

/-- A canonical frame beginning at `p` in cardinal direction `d`. -/
def frameAlong (p : Point) (d : Fin 4) : Frame :=
  ⟨decide (d.val % 2 = 0), decide (2 ≤ d.val), false, p⟩

@[simp] theorem frameAlong_direction (p : Point) (d : Fin 4) :
    (frameAlong p d).axisDirection = d := by
  fin_cases d <;> rfl

def initialRunState (p : Point) (d : Fin 4) : RunState :=
  ⟨frameAlong p d, 0, 0⟩

@[simp] theorem initialRunState_point_zero (p : Point) (d : Fin 4) :
    (initialRunState p d).point 0 = p := by
  change (frameAlong p d).map (0 + 0, 0) = p
  rw [zero_add, Frame.map_zero]
  rfl

/-- The ideal run follows the actual cardinal longitudinal axis of its
current signed frame. -/
theorem RunState.point_advance (s : RunState) (n : Nat) :
    s.point n = LatticeRouteRuns.advance (s.point 0) s.frame.axisDirection n := by
  simpa only [RunState.point, runPoint, add_zero] using
    s.frame.axis_advance (s.phase.val : Int) (s.lane.val : Int) n

theorem RunState.point_int_advance (s : RunState) (k : Int) (hk : 0 ≤ k) :
    s.point k = LatticeRouteRuns.advance (s.point 0) s.frame.axisDirection k.toNat := by
  rw [← Int.toNat_of_nonneg hk]
  exact s.point_advance _

theorem initialRunState_point (p : Point) (d : Fin 4) (n : Nat) :
    (initialRunState p d).point n = LatticeRouteRuns.advance p d n := by
  rw [RunState.point_advance, initialRunState_point_zero]
  exact congrArg (fun e => LatticeRouteRuns.advance p e n) (frameAlong_direction p d)

theorem RunState.advance_direction (s : RunState) (length : Nat) (d : Fin 4)
    (hd : s.frame.axisDirection.val % 2 ≠ d.val % 2) :
    (s.advance length (s.frame.chooseTurn d)).frame.axisDirection = d :=
  s.frame.next_axisDirection (s.length length) d hd

end GridHardness.SignedTentacle
