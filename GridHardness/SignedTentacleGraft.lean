/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleTransform

/-!
# Signed Tentacle Graft

Replace the initial straight strip of a valid signed drawing by an
earlier valid drawing. Exact contact with the added strips and clearance
of their neighbors are sufficient; the earlier drawing is unrestricted
outside that finite neighborhood.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false

theorem Aligned.refl (a : Fin 2 → Point) : Aligned a a := Or.inl ⟨rfl,rfl⟩

theorem Aligned.trans {a b c : Fin 2 → Point} (hab : Aligned a b) (hbc : Aligned b c) :
    Aligned a c := by
  rcases hab with ⟨h0,h1⟩ | ⟨h0,h1⟩ <;> rcases hbc with ⟨k0,k1⟩ | ⟨k0,k1⟩
  · exact Or.inl ⟨h0.trans k0,h1.trans k1⟩
  · exact Or.inr ⟨h0.trans k0,h1.trans k1⟩
  · exact Or.inr ⟨h0.trans k1,h1.trans k0⟩
  · exact Or.inl ⟨h0.trans k1,h1.trans k0⟩

def Drawing.baseFrame : Drawing → Frame
  | .base f _ => f
  | .attach d _ _ => d.baseFrame

def Drawing.baseLength : Drawing → Nat
  | .base _ n => n
  | .attach d _ _ => d.baseLength

def Drawing.basePoints (d : Drawing) : Finset Point := strip d.baseFrame d.baseLength

def Drawing.baseTip (d : Drawing) : Fin 2 → Point := far d.baseFrame d.baseLength

/-- The union of the strips after the initial straight portion. -/
def Drawing.tailPoints : Drawing → Finset Point
  | .base _ _ => ∅
  | .attach d f n => d.tailPoints ∪ strip f n

def Drawing.tailSize : Drawing → Nat
  | .base _ _ => 0
  | .attach d _ n => d.tailSize+n

def Drawing.graft (old : Drawing) : Drawing → Drawing
  | .base _ _ => old
  | .attach d f n => .attach (Drawing.graft old d) f n

theorem Drawing.points_base_tail (d : Drawing) : d.points=d.basePoints ∪ d.tailPoints := by
  induction d with
  | base f n => simp [Drawing.points,Drawing.basePoints,Drawing.baseFrame,
      Drawing.baseLength,Drawing.tailPoints]
  | attach d f n ih => simp only [Drawing.points,Drawing.basePoints,Drawing.baseFrame,
      Drawing.baseLength,Drawing.tailPoints,ih,Finset.union_assoc]

theorem Drawing.tail_subset (d : Drawing) : d.tailPoints ⊆ d.points := by
  rw [d.points_base_tail]
  exact Finset.subset_union_right

theorem Drawing.base_subset (d : Drawing) : d.basePoints ⊆ d.points := by
  rw [d.points_base_tail]
  exact Finset.subset_union_left

theorem Drawing.graft_points (old d : Drawing) :
    (Drawing.graft old d).points=old.points ∪ d.tailPoints := by
  induction d with
  | base f n => simp [Drawing.graft,Drawing.tailPoints]
  | attach d f n ih => simp only [Drawing.graft,Drawing.points,Drawing.tailPoints,
      ih,Finset.union_assoc]

theorem Drawing.graft_start (old d : Drawing) (r : Fin 2) :
    (Drawing.graft old d).start r=old.start r := by
  induction d with
  | base f n => rfl
  | attach d f n ih => exact ih

theorem Drawing.graft_tip_aligned (old d : Drawing) (h : Aligned old.tip d.baseTip) :
    Aligned (Drawing.graft old d).tip d.tip := by
  cases d with
  | base f n => exact h
  | attach d f n => exact Aligned.refl _

theorem Drawing.graft_halfSize (old d : Drawing) :
    (Drawing.graft old d).halfSize=old.halfSize+d.tailSize := by
  induction d with
  | base f n => simp [Drawing.graft,Drawing.tailSize]
  | attach d f n ih => simp only [Drawing.graft,Drawing.halfSize,Drawing.tailSize,ih,Nat.add_assoc]

/-- The old drawing has exactly the original initial strip's contact
with the added strips; any old point adjacent to them also lies in that
initial strip. Both tests concern explicit finite sets. -/
def Drawing.GraftClear (old d : Drawing) : Prop :=
  (∀ p ∈ d.tailPoints, p∈old.points ↔ p∈d.basePoints) ∧
  (∀ p ∈ old.points, ∀ q ∈ d.tailPoints, lattice.Adj p q → p∈d.basePoints)

theorem Drawing.GraftClear.prefix {old d : Drawing} {f : Frame} {n : Nat}
    (h : Drawing.GraftClear old (.attach d f n)) : Drawing.GraftClear old d := by
  exact ⟨fun p hp => h.1 p (Finset.mem_union_left _ hp),
    fun p hp q hq ha => h.2 p hp q (Finset.mem_union_left _ hq) ha⟩

theorem Drawing.GraftClear.new_mem_iff {old d : Drawing} {f : Frame} {n : Nat}
    (h : Drawing.GraftClear old (.attach d f n)) {p : Point} (hp : p ∈strip f n) :
    p∈(Drawing.graft old d).points ↔ p∈d.points := by
  rw [Drawing.graft_points,d.points_base_tail]
  simp only [Finset.mem_union]
  exact or_congr (h.1 p (Finset.mem_union_right _ hp)) Iff.rfl

/-- Local geometric replacement transports every exact overlap and
separation condition of the complete strip chain. -/
theorem Drawing.graft_valid (old d : Drawing) (ho : old.Valid) (hd : d.Valid)
    (ht : Aligned old.tip d.baseTip) (hc : Drawing.GraftClear old d) :
    (Drawing.graft old d).Valid := by
  induction d with
  | base f n => exact ho
  | attach d f n ih =>
    obtain ⟨hd,hn,ha,hi,hs⟩ := hd
    refine ⟨ih hd ht hc.prefix,hn,(Drawing.graft_tip_aligned old d ht).trans ha,?_,?_⟩
    · rw [← hi]
      ext p
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hp,hq⟩
        exact ⟨(hc.new_mem_iff hq).mp hp,hq⟩
      · rintro ⟨hp,hq⟩
        exact ⟨(hc.new_mem_iff hq).mpr hp,hq⟩
    · intro p hp q hq hadj
      have hp' : p∈d.points := by
        rw [Drawing.graft_points,Finset.mem_union] at hp
        rcases hp with hp | hp
        · exact d.base_subset (hc.2 p hp q (Finset.mem_union_right _ hq) hadj)
        · exact d.tail_subset hp
      rcases hs p hp' q hq hadj with hh | hh
      · exact Or.inl hh
      · exact Or.inr ((hc.new_mem_iff hq).mpr hh)

theorem Drawing.graft_card (old d : Drawing) (ho : old.Valid) (hd : d.Valid)
    (ht : Aligned old.tip d.baseTip) (hc : Drawing.GraftClear old d) :
    (Drawing.graft old d).points.card=old.points.card+2*d.tailSize := by
  rw [Drawing.card _ (Drawing.graft_valid old d ho hd ht hc),Drawing.card _ ho,
    Drawing.graft_halfSize]
  omega

end GridHardness.SignedTentacle
