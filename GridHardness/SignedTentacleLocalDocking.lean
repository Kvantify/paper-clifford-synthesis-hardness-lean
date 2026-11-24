/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleInverse
public import GridHardness.SignedTentacleRunDocking

/-!
# Signed Tentacle Local Docking

Recover local syntactic docking from a globally positioned initial
frame and geometric clearance of every later strip.
-/

public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false

@[simp] theorem Drawing.graft_baseFrame (old d : Drawing) :
    (Drawing.graft old d).baseFrame=old.baseFrame := by
  induction d with
  | base g n => rfl
  | attach d g n ih => exact ih

@[simp] theorem Drawing.graft_tailPoints (old d : Drawing) :
    (Drawing.graft old d).tailPoints=old.tailPoints∪d.tailPoints := by
  induction d with
  | base g n => simp [Drawing.graft,Drawing.tailPoints]
  | attach d g n ih => simp only [Drawing.graft,Drawing.tailPoints,ih,Finset.union_assoc]

/-- The local certificate tracks the initial frame and all later strips,
not merely the point-set boundary of the whole drawing. -/
theorem Drawing.local_docked (f : Frame) (side : Fin 4) (d : Drawing)
    (hb : d.baseFrame = f.comp (NineClusterAttachment.dock true side))
    (ht : ∀ p ∈ d.tailPoints, 4 ≤IntegerGrid.manhattan (f.map (1, 1)) p) :
    NineClusterAttachment.Docked true side (Drawing.transform f.inverse d) := by
  rw [NineClusterAttachment.docked_iff_base_tail]
  constructor
  · rw [Drawing.transform_baseFrame,hb,Frame.inverse_comp_comp]
  · apply NineClusterAttachment.clear_of_center_distance
    intro p hp
    rw [Drawing.transform_tailPoints] at hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hd := f.inverse.distance (f.map (1,1)) q
    have hh := ht q hq
    rw [← hd] at hh
    simpa only [Frame.inverse_map,Frame.unmap_map] using hh

end GridHardness.SignedTentacle
