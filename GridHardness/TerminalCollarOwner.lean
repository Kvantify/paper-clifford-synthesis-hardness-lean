/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TerminalCollarAttach
public import GridHardness.GridAssemblyLocal
public import GridHardness.SignedTentacleInverse

/-!
# Terminal Collar Owner

Preserve an owner's concrete docking certificate while adding a
recipient collar. The new strips are confined near the distant recipient,
so they are clear of the owner's nine-cluster. The resulting drawing is
therefore a valid arm of the existing global assembly interface.
-/

public section

namespace GridHardness
open CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false

theorem NineClusterAttachment.Clear.mono {S T : Finset Point}
    (h : NineClusterAttachment.Clear T) (hst : S ⊆ T) : NineClusterAttachment.Clear S := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp h.1 hp (hst hq)
  · intro c hc p hp ha
    exact h.2 c hc p (hst hp) ha

/-- A graft retains the old initial dock and appends only strips from
the certified new tail. -/
theorem NineClusterAttachment.Docked.graft (old d : Drawing) (b : Bool) (s : Fin 4)
    (h : NineClusterAttachment.Docked b s old)
    (hc : NineClusterAttachment.Clear d.tailPoints) :
    NineClusterAttachment.Docked b s (Drawing.graft old d) := by
  induction d with
  | base f n => exact h
  | attach d f n ih =>
    exact ⟨ih (hc.mono Finset.subset_union_left),hc.mono Finset.subset_union_right⟩

namespace TerminalCollarAttach

theorem owner_radius (p : Point) (hp : p ∈ NineClusterAttachment.points) :
    IntegerGrid.manhattan (1,1) p≤2 := by
  have hb := (NineClusterAttachment.mem_points_iff p).mp hp
  dsimp [IntegerGrid.manhattan]
  omega

/-- Eighteen steps between the owner center and recipient anchor
already leave two steps of clearance around the new radius-fourteen tail. -/
theorem owner_tail_distance (a : Point) (s : Fin 4) (b : Bool)
    (ha : 18 ≤ IntegerGrid.manhattan (1, 1) a) (p q : Point)
    (hp : p ∈ NineClusterAttachment.points)
    (hq : q ∈ (TerminalCollarMatched.tail s b).image (shift a).map) :
    2≤IntegerGrid.manhattan p q := by
  have hp' := owner_radius p hp
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
  have hr' := TerminalCollarMatched.tail_radius s b r hr
  have hd := (shift a).distance (0,0) r
  rw [Frame.map_zero] at hd
  change IntegerGrid.manhattan a ((shift a).map r)=IntegerGrid.manhattan (0,0) r at hd
  have h1 := IntegerGrid.manhattan_triangle (1,1) p a
  have h2 := IntegerGrid.manhattan_triangle p ((shift a).map r) a
  rw [IntegerGrid.manhattan_comm ((shift a).map r) a,hd] at h2
  omega

theorem owner_tail_clear (a : Point) (s : Fin 4) (b : Bool)
    (ha : 18 ≤ IntegerGrid.manhattan (1, 1) a) :
    NineClusterAttachment.Clear ((TerminalCollarMatched.tail s b).image (shift a).map) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    have h := owner_tail_distance a s b ha p p hp hq
    simp [IntegerGrid.manhattan] at h
  · intro p hp q hq he
    have h := owner_tail_distance a s b ha p q hp hq
    change IntegerGrid.manhattan p q=1 at he
    omega

/-- Recipient attachment preserves the owner's exact syntactic dock. -/
theorem docked (a : Point) (old : Drawing) (ownerSide s : Fin 4) (lane : Fin 2)
    (ho : NineClusterAttachment.Docked true ownerSide old)
    (ha : 18 ≤ IntegerGrid.manhattan (1, 1) a) :
    NineClusterAttachment.Docked true ownerSide (attach a old s lane) := by
  rw [attach_eq_graft]
  apply NineClusterAttachment.Docked.graft _ _ true ownerSide ho
  rw [Drawing.transform_tailPoints]
  exact owner_tail_clear a s (phase a old s lane) ha

/-- The complete owner-to-recipient drawing meets the exact existing
`Arm.Valid` interface, rather than only a route-level assertion. -/
theorem arm_valid (a : Point) (old : Drawing) (ownerSide s : Fin 4) (lane : Fin 2)
    (ho : old.Valid) (hDock : NineClusterAttachment.Docked true ownerSide old)
    (hd : old.lastFrame.axisDirection = s)
    (he : old.tip lane = (shift a).map (TerminalCollarMatch.innerPoint s))
    (hl : BoxLocality a old) (ha : 18 ≤ IntegerGrid.manhattan (1, 1) a) :
    GridAssembly.Arm.Valid (some (ownerSide,attach a old s lane)) :=
  ⟨valid a old s lane ho hd he hl,docked a old ownerSide s lane hDock ha⟩

/-- The designated output lane has the checkerboard phase of the
recipient anchor, independently of the chosen transverse template. -/
theorem tip_color (a : Point) (old : Drawing) (s : Fin 4) (lane : Fin 2) :
    color ((attach a old s lane).tip 0)=(a.1+a.2)%2 := by
  rw [tip,TerminalCollarRotations.tip_coordinates]
  fin_cases s <;> simp [shift,Frame.map,place,sign,color] <;> omega

theorem arm_port (a : Point) (old : Drawing) (ownerSide s : Fin 4) (lane : Fin 2)
    (f : Frame) (ha : (a.1 + a.2) % 2=0) :
    GridAssembly.armPort f (some (ownerSide,attach a old s lane))
      (f.map ((attach a old s lane).tip 0)) := by
  exact ⟨rfl,(tip_color a old s lane).trans ha⟩

end TerminalCollarAttach
end GridHardness
