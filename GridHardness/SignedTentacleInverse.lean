/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleGraft

/-!
# Signed Tentacle Inverse

Inverse signed placements let a globally constructed strip chain be
viewed in the local coordinates of its owning cluster.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false

/-- The signed coordinate inverse, itself represented by a frame. -/
def Frame.inverse (f : Frame) : Frame where
  horizontal := f.horizontal
  reverseX := if f.horizontal then f.reverseX else f.reverseY
  reverseY := if f.horizontal then f.reverseY else f.reverseX
  origin := f.unmap (0,0)

@[simp] theorem Frame.inverse_map (f : Frame) (p : Point) :
    f.inverse.map p = f.unmap p := by
  rcases f with ⟨h,x,y,o⟩
  cases h <;> cases x <;> cases y <;>
    apply Prod.ext <;> simp [Frame.inverse,Frame.map,Frame.unmap,place,sign] <;> omega

@[simp] theorem Frame.comp_inverse_comp (f g : Frame) : f.comp (f.inverse.comp g)=g := by
  rcases f with ⟨h,x,y,o⟩
  rcases g with ⟨h',x',y',o'⟩
  cases h <;> cases x <;> cases y <;> cases h' <;> cases x' <;> cases y' <;>
    simp [Frame.comp,Frame.inverse,Frame.map,Frame.unmap,place,sign]

@[simp] theorem Frame.inverse_comp_comp (f g : Frame) : f.inverse.comp (f.comp g)=g := by
  rcases f with ⟨h,x,y,o⟩
  rcases g with ⟨h',x',y',o'⟩
  cases h <;> cases x <;> cases y <;> cases h' <;> cases x' <;> cases y' <;>
    simp [Frame.comp,Frame.inverse,Frame.map,Frame.unmap,place,sign]

@[simp] theorem Drawing.transform_inverse (f : Frame) (d : Drawing) :
    Drawing.transform f (Drawing.transform f.inverse d)=d := by
  induction d with
  | base g n => simp [Drawing.transform]
  | attach d g n ih => simp [Drawing.transform,ih]

@[simp] theorem Drawing.inverse_transform (f : Frame) (d : Drawing) :
    Drawing.transform f.inverse (Drawing.transform f d)=d := by
  induction d with
  | base g n => simp [Drawing.transform]
  | attach d g n ih => simp [Drawing.transform,ih]

@[simp] theorem Drawing.transform_baseFrame (f : Frame) (d : Drawing) :
    (Drawing.transform f d).baseFrame=f.comp d.baseFrame := by
  induction d with
  | base g n => rfl
  | attach d g n ih => exact ih

@[simp] theorem Drawing.transform_tailPoints (f : Frame) (d : Drawing) :
    (Drawing.transform f d).tailPoints=d.tailPoints.image f.map := by
  induction d with
  | base g n => simp [Drawing.transform,Drawing.tailPoints]
  | attach d g n ih => simp [Drawing.transform,Drawing.tailPoints,ih,Finset.image_union]

end GridHardness.SignedTentacle
