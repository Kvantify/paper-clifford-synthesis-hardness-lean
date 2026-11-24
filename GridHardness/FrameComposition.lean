/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleFrame

/-!
# Frame Composition

Composition of signed orthogonal placements. Nested cluster/tentacle
frames can be serialized as a single frame without enumerating coordinates.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false

/-- `f.comp g` first applies `g`, then `f`. -/
def Frame.comp (f g : Frame) : Frame where
  horizontal := f.horizontal == g.horizontal
  reverseX := g.reverseX ^^ (if g.horizontal then f.reverseX else f.reverseY)
  reverseY := g.reverseY ^^ (if g.horizontal then f.reverseY else f.reverseX)
  origin := f.map g.origin

@[simp] theorem Frame.map_comp (f g : Frame) (p : Point) :
    (f.comp g).map p = f.map (g.map p) := by
  rcases f with ⟨fh, fx, fy, fo⟩
  rcases g with ⟨gh, gx, gy, go⟩
  cases fh <;> cases fx <;> cases fy <;> cases gh <;> cases gx <;> cases gy <;>
    simp [Frame.comp, Frame.map, place, sign, Int.add_assoc]
  all_goals omega

/-- Composition preserves the represented finite point set exactly. -/
theorem Frame.image_comp (f g : Frame) (S : Finset Point) :
    S.image (f.comp g).map = (S.image g.map).image f.map := by
  rw [Finset.image_image]
  congr 1
  funext p
  exact f.map_comp g p

@[simp] theorem Frame.map_zero (f : Frame) : f.map (0, 0) = f.origin := by
  cases f with
  | mk h x y o => cases h <;> cases x <;> cases y <;> simp [Frame.map, place, sign]

/-- A coordinate-magnitude estimate for later concrete drawing bounds. -/
theorem Frame.origin_comp_bound (f g : Frame) :
    IntegerGrid.manhattan (0, 0) (f.comp g).origin ≤
      IntegerGrid.manhattan (0, 0) f.origin + IntegerGrid.manhattan (0, 0) g.origin := by
  have h := IntegerGrid.manhattan_triangle (0, 0) f.origin (f.map g.origin)
  have hd := f.distance (0, 0) g.origin
  rw [f.map_zero] at hd
  simpa only [Frame.comp, hd] using h

end GridHardness.SignedTentacle
