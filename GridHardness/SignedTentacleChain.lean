/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleTurns
public import GridHardness.ClusterStar

/-!
# Signed Tentacle Chain

Extend an existing signed strip chain by a concrete turn. The adjacent
strip geometry is discharged by the turn construction; only separation
from the earlier strips remains to be supplied by the global route geometry.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false

def Drawing.lastFrame : Drawing → Frame
  | .base f _ => f
  | .attach _ f _ => f

def Drawing.lastLength : Drawing → Nat
  | .base _ n => n
  | .attach _ _ n => n

/-- Earlier strips, before the terminal strip. -/
def Drawing.prefixPoints : Drawing → Finset Point
  | .base _ _ => ∅
  | .attach d _ _ => d.points

theorem Drawing.points_prefix (d : Drawing) :
    d.points=d.prefixPoints ∪ strip d.lastFrame d.lastLength := by
  cases d <;> simp [Drawing.points,Drawing.prefixPoints,Drawing.lastFrame,Drawing.lastLength]

theorem Drawing.tip_last (d : Drawing) : d.tip=far d.lastFrame d.lastLength := by
  cases d <;> rfl

theorem Drawing.lastLength_ge_three (d : Drawing) (h : d.Valid) : 3≤d.lastLength := by
  cases d with
  | base f n => exact h
  | attach d f n => exact h.2.1

def Drawing.turn (d : Drawing) (down : Bool) (n : Nat) : Drawing :=
  .attach d (nextFrame d.lastFrame d.lastLength down) n

/-- Local turn geometry plus clearance from all earlier strips suffices
for the full recursive validity condition. -/
theorem Drawing.turn_valid (d : Drawing) (hd : d.Valid) (down : Bool) (n : Nat) (hn : 3 ≤ n)
    (hclear : ClusterStar.Apart d.prefixPoints
      (strip (nextFrame d.lastFrame d.lastLength down) n)) :
    (d.turn down n).Valid := by
  refine ⟨hd,hn,?_,?_,?_⟩
  · rw [d.tip_last]
    exact nextFrame_aligned d.lastFrame d.lastLength down
  · rw [d.points_prefix,Finset.union_inter_distrib_right,
      Finset.disjoint_iff_inter_eq_empty.mp hclear.1,Finset.empty_union]
    exact nextFrame_overlap d.lastFrame d.lastLength n down (by omega)
  · intro p hp q hq ha
    rw [d.points_prefix,Finset.mem_union] at hp
    rcases hp with hp | hp
    · exact False.elim (hclear.2 p hp q hq ha)
    · have hh := nextFrame_separated d.lastFrame d.lastLength n down p hp q hq ha
      exact hh.imp id (fun hm => by rw [d.points_prefix]; exact Finset.mem_union_right _ hm)

@[simp] theorem Drawing.turn_start (d : Drawing) (down : Bool) (n : Nat) (r : Fin 2) :
    (d.turn down n).start r=d.start r := rfl

@[simp] theorem Drawing.turn_halfSize (d : Drawing) (down : Bool) (n : Nat) :
    (d.turn down n).halfSize=d.halfSize+n := rfl

/-- Initial cluster docking persists when the new strip is clear of the cluster. -/
theorem Drawing.turn_docked (d : Drawing) (b : Bool) (side : Fin 4)
    (hd : NineClusterAttachment.Docked b side d) (down : Bool) (n : Nat)
    (hc : NineClusterAttachment.Clear (strip (nextFrame d.lastFrame d.lastLength down) n)) :
    NineClusterAttachment.Docked b side (d.turn down n) := ⟨hd,hc⟩

end GridHardness.SignedTentacle
