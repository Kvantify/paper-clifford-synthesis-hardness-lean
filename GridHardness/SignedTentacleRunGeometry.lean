/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleTurns

/-!
# Signed Tentacle Run Geometry

The longitudinal phase needed when a width-two strip follows a finite
orthogonal run.  A southward turn reverses the shared rung, so the next
ideal corner is one unit along its strip rather than necessarily at its
origin. Tracking this bit makes the ideal vertices agree exactly at every
turn; no displacement accumulates along a route.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The position of the chosen ideal lane on the next joining edge. -/
def turnPhase (down : Bool) (lane : Fin 2) : Fin 2 :=
  if down then ⟨1 - lane.val, by have := lane.is_lt; omega⟩ else lane

@[simp] theorem turnPhase_false (lane : Fin 2) : turnPhase false lane = lane := rfl

@[simp] theorem turnPhase_true_val (lane : Fin 2) :
    (turnPhase true lane).val = 1 - lane.val := rfl

/-- A phase-zero strip begins at the ideal start. A phase-one strip has
one additional point before that start, to accommodate the preceding turn. -/
def runLength (phase : Fin 2) (length : Nat) : Nat := phase.val + length

/-- The finite ideal centerline is obtained by restricting `k` to the
integer interval from zero to the run length. -/
def runPoint (f : Frame) (phase lane : Fin 2) (k : Int) : Point :=
  f.map ((phase.val : Int) + k, (lane.val : Int))

theorem runLength_bounds (phase : Fin 2) (length : Nat) :
    length ≤ runLength phase length ∧ runLength phase length ≤ length + 1 := by
  have := phase.is_lt
  dsimp [runLength]
  omega

theorem runLength_three (phase : Fin 2) (length : Nat) (hl : 3 ≤ length) :
    3 ≤ runLength phase length := by
  have := (runLength_bounds phase length).1
  omega

/-- Moving along the axis of the next strip means moving in the chosen
perpendicular direction from the old ideal lane. This identity includes
the phase correction at the joining edge. -/
theorem nextFrame_phase_axis (f : Frame) (a : Nat) (down : Bool)
    (lane : Fin 2) (k : Int) :
    (nextFrame f a down).map (((turnPhase down lane).val : Int) + k, 0) =
      f.map ((a : Int), (lane.val : Int) + sign down k) := by
  rw [nextFrame, Frame.map_comp]
  congr 1
  cases down <;> fin_cases lane <;>
    simp [turnFrame, turnPhase, Frame.map, place, sign]

/-- The next run starts exactly at the previous run's ideal endpoint,
even when reversal of the joining rung changes its longitudinal phase. -/
theorem run_corner (f : Frame) (phase lane : Fin 2) (length : Nat)
    (down : Bool) :
    runPoint (nextFrame f (runLength phase length) down) (turnPhase down lane) 0 0 =
      runPoint f phase lane length := by
  simp only [runPoint, Fin.val_zero, Int.natCast_zero]
  rw [nextFrame_phase_axis]
  simp [runLength, sign]

/-- Exact geometry for every point along the next ideal run. The new
run has lane zero, and its start phase is the previous turn's bit. -/
theorem run_after_turn (f : Frame) (phase lane : Fin 2) (length : Nat)
    (down : Bool) (k : Int) :
    runPoint (nextFrame f (runLength phase length) down) (turnPhase down lane) 0 k =
      f.map ((phase.val : Int) + length, (lane.val : Int) + sign down k) := by
  simp only [runPoint, Fin.val_zero, Int.natCast_zero]
  rw [nextFrame_phase_axis]
  simp [runLength]

/-- Every strip point lies within distance two of the finite ideal run.
The possible one-unit prefix is clamped to the ideal start; the opposite
lane contributes at most one further unit. -/
theorem run_strip_distance (f : Frame) (phase lane : Fin 2) (length : Nat)
    (p : Point) (hp : p ∈ strip f (runLength phase length)) :
    ∃ k : Int, 0 ≤ k ∧ k ≤ length ∧
      IntegerGrid.manhattan p (runPoint f phase lane k) ≤ 2 := by
  have hm := (mem_strip_iff f (runLength phase length) p).mp hp
  have hh := phase.is_lt
  have hr := lane.is_lt
  simp only [runLength, Nat.cast_add] at hm
  by_cases hx : (phase.val : Int) ≤ (f.unmap p).1
  · refine ⟨(f.unmap p).1 - phase.val, by omega, by omega, ?_⟩
    have hd := f.distance (f.unmap p)
      ((phase.val : Int) + ((f.unmap p).1 - phase.val), (lane.val : Int))
    rw [f.map_unmap] at hd
    rw [runPoint, hd]
    simp only [IntegerGrid.manhattan]
    omega
  · refine ⟨0, by omega, by omega, ?_⟩
    have hd := f.distance (f.unmap p) ((phase.val : Int) + 0, (lane.val : Int))
    rw [f.map_unmap] at hd
    rw [runPoint, hd]
    simp only [IntegerGrid.manhattan]
    omega

/-- On phase-zero runs the finite centerline already covers the whole
longitudinal extent, so only the one-unit lane width is needed. -/
theorem run_strip_distance_zero (f : Frame) (lane : Fin 2) (length : Nat)
    (p : Point) (hp : p ∈ strip f (runLength 0 length)) :
    ∃ k : Int, 0 ≤ k ∧ k ≤ length ∧
      IntegerGrid.manhattan p (runPoint f 0 lane k) ≤ 1 := by
  have hm := (mem_strip_iff f (runLength 0 length) p).mp hp
  have hr := lane.is_lt
  simp only [runLength, Fin.val_zero, zero_add] at hm
  refine ⟨(f.unmap p).1, hm.1, hm.2.1, ?_⟩
  have hd := f.distance (f.unmap p) ((f.unmap p).1, (lane.val : Int))
  rw [f.map_unmap] at hd
  simp only [runPoint, Fin.val_zero, Int.natCast_zero, zero_add]
  rw [hd]
  simp only [IntegerGrid.manhattan]
  omega

/-- Phase correction never spoils the minimum strip length. -/
theorem run_turn_valid (f : Frame) (phase lane : Fin 2) (length nextLength : Nat)
    (down : Bool) (hl : 3 ≤ length) (hn : 3 ≤ nextLength) :
    (Drawing.attach (.base f (runLength phase length))
      (nextFrame f (runLength phase length) down)
      (runLength (turnPhase down lane) nextLength)).Valid :=
  nextFrame_pair_valid f _ _ down (runLength_three phase length hl)
    (runLength_three (turnPhase down lane) nextLength hn)

/-- The finite state carried between consecutive ideal straight runs.
Its coordinates locate the ideal start, not merely a nearby lattice point. -/
structure RunState where
  frame : Frame
  phase : Fin 2
  lane : Fin 2
  deriving DecidableEq

def RunState.point (s : RunState) (k : Int) : Point :=
  runPoint s.frame s.phase s.lane k

def RunState.length (s : RunState) (length : Nat) : Nat := runLength s.phase length

/-- Advance through a run and a signed right-angle turn. -/
def RunState.advance (s : RunState) (length : Nat) (down : Bool) : RunState where
  frame := nextFrame s.frame (s.length length) down
  phase := turnPhase down s.lane
  lane := 0

/-- Consecutive ideal segments meet at the same lattice point exactly. -/
theorem RunState.advance_start (s : RunState) (length : Nat) (down : Bool) :
    (s.advance length down).point 0 = s.point length :=
  run_corner s.frame s.phase s.lane length down

theorem RunState.advance_point (s : RunState) (length : Nat) (down : Bool) (k : Int) :
    (s.advance length down).point k =
      s.frame.map ((s.phase.val : Int) + length, (s.lane.val : Int) + sign down k) :=
  run_after_turn s.frame s.phase s.lane length down k

theorem RunState.strip_distance (s : RunState) (length : Nat) (p : Point)
    (hp : p ∈ strip s.frame (s.length length)) :
    ∃ k : Int, 0 ≤ k ∧ k ≤ length ∧ IntegerGrid.manhattan p (s.point k) ≤ 2 :=
  run_strip_distance s.frame s.phase s.lane length p hp

theorem RunState.advance_pair_valid (s : RunState) (length nextLength : Nat)
    (down : Bool) (hl : 3 ≤ length) (hn : 3 ≤ nextLength) :
    (Drawing.attach (.base s.frame (s.length length))
      (s.advance length down).frame ((s.advance length down).length nextLength)).Valid :=
  run_turn_valid s.frame s.phase s.lane length nextLength down hl hn

end GridHardness.SignedTentacle
