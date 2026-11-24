/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleU
public import GridHardness.SignedTentacleTransform

/-!
# Signed Tentacle Turns

Both signed right-angle continuations of a strip.  The new strip lies
on the outward side of the preceding far rung.  This choice is essential:
choosing the opposite transverse orientation would create a four-point
overlap instead of the two-point interface required by `Drawing.Valid`.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- `false` continues north and `true` continues south from an eastward
strip. In both cases the new strip extends east of the shared rung. -/
def turnFrame (a : Nat) (down : Bool) : Frame :=
  ⟨false, down, false, (a, if down then 1 else 0)⟩

@[simp] theorem turnFrame_false (a : Nat) : turnFrame a false = northFrame a := rfl

theorem mem_turnFrame (a b : Nat) (down : Bool) (p : Point) :
    p ∈ strip (turnFrame a down) b ↔
    (a : Int) ≤ p.1 ∧ p.1 ≤ (a : Int) + 1 ∧
      (if down then 1 - (b : Int) ≤ p.2 ∧ p.2 ≤ 1
       else 0 ≤ p.2 ∧ p.2 ≤ b) := by
  cases down <;>
    simp only [mem_strip_iff, turnFrame, Frame.unmap, sign, ite_true,
      Bool.false_eq_true, ite_false] <;> omega

theorem turn_aligned (a : Nat) (down : Bool) :
    Aligned (far eastFrame a) (join (turnFrame a down)) := by
  cases down
  · left
    constructor <;> simp [far, join, turnFrame, eastFrame, Frame.map, place, sign]
  · right
    constructor <;> simp [far, join, turnFrame, eastFrame, Frame.map, place, sign]

theorem turn_overlap (a b : Nat) (down : Bool) (hb : 1 ≤ b) :
    strip eastFrame a ∩ strip (turnFrame a down) b =
      {join (turnFrame a down) 0, join (turnFrame a down) 1} := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [Finset.mem_inter, mem_east, mem_turnFrame,
    Finset.mem_insert, Finset.mem_singleton]
  cases down <;>
    simp only [join, turnFrame, Frame.map, place, sign, Bool.false_eq_true,
      ite_false, ite_true, Fin.val_zero, Fin.val_one, Int.natCast_zero,
      Int.natCast_one, add_zero, neg_zero, Prod.mk.injEq] <;> omega

theorem turn_separated (a b : Nat) (down : Bool) :
    Separated (strip eastFrame a) (strip (turnFrame a down) b) := by
  intro p hp q hq ha
  rw [mem_east] at hp
  rw [mem_turnFrame] at hq
  change IntegerGrid.manhattan p q = 1 at ha
  rw [manhattan_one_iff] at ha
  rw [mem_turnFrame, mem_east]
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  simp only [Prod.mk.injEq] at ha
  dsimp at hp hq ⊢
  cases down <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hq ⊢ <;> omega

/-- The two-strip construction with either signed turn. -/
def turnPair (a b : Nat) (down : Bool) : Drawing :=
  .attach (.base eastFrame a) (turnFrame a down) b

theorem turnPair_valid (a b : Nat) (down : Bool) (ha : 3 ≤ a) (hb : 3 ≤ b) :
    (turnPair a b down).Valid :=
  ⟨ha, hb, turn_aligned a down, turn_overlap a b down (by omega),
    turn_separated a b down⟩

/-- Each point of a signed strip lies at distance at most one from its
longitudinal axis, with an integer axis parameter in the stated range. -/
theorem strip_axis_distance (f : Frame) (n : Nat) (p : Point)
    (hp : p ∈ strip f n) :
    ∃ k : Int, 0 ≤ k ∧ k ≤ n ∧
      IntegerGrid.manhattan p (f.map (k, 0)) ≤ 1 := by
  have hm := (mem_strip_iff f n p).mp hp
  refine ⟨(f.unmap p).1, hm.1, hm.2.1, ?_⟩
  have hd := f.distance (f.unmap p) ((f.unmap p).1, 0)
  rw [f.map_unmap] at hd
  rw [hd]
  simp only [IntegerGrid.manhattan, sub_self, sub_zero]
  omega

/-- The signed turn stays within distance two of the ideal centerline
which turns at `(a,0)`. The one-unit southward phase adjustment accounts
for the reversal of the shared rung. -/
theorem turn_axis_distance (a b : Nat) (down : Bool) (p : Point)
    (hp : p ∈ strip (turnFrame a down) b) :
    ∃ k : Int, 0 ≤ k ∧ k ≤ b ∧
      IntegerGrid.manhattan p ((a : Int), sign down k) ≤ 2 := by
  have hm := (mem_strip_iff (turnFrame a down) b p).mp hp
  refine ⟨((turnFrame a down).unmap p).1, hm.1, hm.2.1, ?_⟩
  have he := (turnFrame a down).map_unmap p
  rcases p with ⟨x, y⟩
  cases down <;>
    simp only [turnFrame, Frame.unmap, Frame.map, sign, place, ite_true,
      Bool.false_eq_true, ite_false, Prod.mk.injEq] at hm he ⊢ <;>
    simp only [IntegerGrid.manhattan] <;> omega

/-- The explicit continuation frame in arbitrary signed coordinates. -/
def nextFrame (f : Frame) (a : Nat) (down : Bool) : Frame :=
  f.comp (turnFrame a down)

@[simp] theorem comp_eastFrame (f : Frame) : f.comp eastFrame = f := by
  rcases f with ⟨h, x, y, o⟩
  cases h <;> cases x <;> cases y <;>
    simp [Frame.comp, eastFrame, Frame.map, place, sign]

theorem nextFrame_aligned (f : Frame) (a : Nat) (down : Bool) :
    Aligned (far f a) (join (nextFrame f a down)) := by
  have h := (turn_aligned a down).transform f
  simpa only [nextFrame, ← far_comp, ← join_comp, comp_eastFrame] using h

theorem nextFrame_overlap (f : Frame) (a b : Nat) (down : Bool) (hb : 1 ≤ b) :
    strip f a ∩ strip (nextFrame f a down) b =
      {join (nextFrame f a down) 0, join (nextFrame f a down) 1} := by
  have h := congrArg (fun S : Finset Point => S.image f.map) (turn_overlap a b down hb)
  rw [Finset.image_inter _ _ f.injective] at h
  simpa only [nextFrame, ← strip_comp, comp_eastFrame, Finset.image_insert, Finset.image_singleton,
    ← join_comp] using h

theorem nextFrame_separated (f : Frame) (a b : Nat) (down : Bool) :
    Separated (strip f a) (strip (nextFrame f a down) b) := by
  have h := (turn_separated a b down).transform f
  simpa only [nextFrame, ← strip_comp, comp_eastFrame] using h

/-- Arbitrarily translated, rotated or reflected local turn certificate. -/
theorem nextFrame_pair_valid (f : Frame) (a b : Nat) (down : Bool)
    (ha : 3 ≤ a) (hb : 3 ≤ b) :
    (Drawing.attach (.base f a) (nextFrame f a down) b).Valid :=
  ⟨ha, hb, nextFrame_aligned f a down, nextFrame_overlap f a b down (by omega),
    nextFrame_separated f a b down⟩

theorem nextFrame_axis_distance (f : Frame) (a b : Nat) (down : Bool)
    (p : Point) (hp : p ∈ strip (nextFrame f a down) b) :
    ∃ k : Int, 0 ≤ k ∧ k ≤ b ∧
      IntegerGrid.manhattan p (f.map ((a : Int), sign down k)) ≤ 2 := by
  obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hp
  have hq' : (turnFrame a down).map q ∈ strip (turnFrame a down) b :=
    Finset.mem_image.mpr ⟨q, hq, rfl⟩
  obtain ⟨k, hk0, hkb, hk⟩ := turn_axis_distance a b down _ hq'
  refine ⟨k, hk0, hkb, ?_⟩
  rw [← he]
  simpa only [nextFrame, Frame.map_comp, Frame.distance] using hk

end GridHardness.SignedTentacle
