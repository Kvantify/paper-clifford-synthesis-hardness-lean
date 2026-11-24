/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacle
public import GridHardness.FrameComposition

/-!
# Signed Tentacle Transform

Signed isometries act on whole strip chains, preserving their exact
point sets and every geometric validity condition. This lets a single local
turn or collar certificate be used in any lattice orientation.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis OrthogonalTentacle
set_option autoImplicit false

@[simp] theorem Frame.adj_iff (f : Frame) (p q : Point) :
    lattice.Adj (f.map p) (f.map q) ↔ lattice.Adj p q := by
  change IntegerGrid.manhattan (f.map p) (f.map q)=1 ↔ _
  rw [f.distance]
  rfl

@[simp] theorem Frame.map_mem_image (f : Frame) (p : Point) (S : Finset Point) :
    f.map p∈S.image f.map ↔ p∈S := by simp [Finset.mem_image,f.injective.eq_iff]

@[simp] theorem strip_comp (f g : Frame) (n : Nat) :
    strip (f.comp g) n=(strip g n).image f.map := f.image_comp g _

@[simp] theorem near_comp (f g : Frame) (r : Fin 2) :
    near (f.comp g) r=f.map (near g r) := f.map_comp g _

@[simp] theorem join_comp (f g : Frame) (r : Fin 2) :
    join (f.comp g) r=f.map (join g r) := f.map_comp g _

@[simp] theorem far_comp (f g : Frame) (n : Nat) (r : Fin 2) :
    far (f.comp g) n r=f.map (far g n r) := f.map_comp g _

theorem Aligned.transform (f : Frame) {a b : Fin 2 → Point} (h : Aligned a b) :
    Aligned (fun r => f.map (a r)) (fun r => f.map (b r)) := by
  rcases h with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact Or.inl ⟨congrArg f.map h0,congrArg f.map h1⟩
  · exact Or.inr ⟨congrArg f.map h0,congrArg f.map h1⟩

@[simp] theorem aligned_transform_iff (f : Frame) (a b : Fin 2 → Point) :
    Aligned (fun r => f.map (a r)) (fun r => f.map (b r)) ↔ Aligned a b := by
  simp only [Aligned,f.injective.eq_iff]

theorem Separated.transform (f : Frame) {S T : Finset Point} (h : Separated S T) :
    Separated (S.image f.map) (T.image f.map) := by
  rintro p hp q hq ha
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
  exact (h u hu v hv ((f.adj_iff u v).mp ha)).imp
    (fun hm => Finset.mem_image.mpr ⟨u,hm,rfl⟩)
    (fun hm => Finset.mem_image.mpr ⟨v,hm,rfl⟩)

@[simp] theorem separated_transform_iff (f : Frame) (S T : Finset Point) :
    Separated (S.image f.map) (T.image f.map) ↔ Separated S T := by
  constructor
  · intro h p hp q hq ha
    have hh := h (f.map p) (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
      (f.map q) (Finset.mem_image.mpr ⟨q,hq,rfl⟩) (f.hom.map_adj ha)
    simpa only [f.map_mem_image] using hh
  · exact Separated.transform f

/-- Apply a single signed placement to every strip of the drawing. -/
def Drawing.transform (f : Frame) : Drawing → Drawing
  | .base g n => .base (f.comp g) n
  | .attach d g n => .attach (Drawing.transform f d) (f.comp g) n

@[simp] theorem Drawing.transform_points (f : Frame) (d : Drawing) :
    (Drawing.transform f d).points=d.points.image f.map := by
  induction d with
  | base g n => exact strip_comp f g n
  | attach d g n ih =>
    simp only [Drawing.transform,Drawing.points,ih,strip_comp,Finset.image_union]

@[simp] theorem Drawing.transform_start (f : Frame) (d : Drawing) (r : Fin 2) :
    (Drawing.transform f d).start r=f.map (d.start r) := by
  induction d with
  | base g n => exact near_comp f g r
  | attach d g n ih => exact ih

@[simp] theorem Drawing.transform_tip (f : Frame) (d : Drawing) (r : Fin 2) :
    (Drawing.transform f d).tip r=f.map (d.tip r) := by
  cases d <;> exact far_comp _ _ _ _

@[simp] theorem Drawing.transform_halfSize (f : Frame) (d : Drawing) :
    (Drawing.transform f d).halfSize=d.halfSize := by
  induction d with
  | base g n => rfl
  | attach d g n ih => simp only [Drawing.transform,Drawing.halfSize,ih]

/-- Every validity condition is invariant, including exact two-point
overlap and the exclusion of extra interior edges. -/
@[simp] theorem Drawing.transform_valid_iff (f : Frame) (d : Drawing) :
    (Drawing.transform f d).Valid ↔ d.Valid := by
  induction d with
  | base g n => rfl
  | attach d g n ih =>
    simp only [Drawing.transform,Drawing.Valid,ih,Drawing.transform_points,strip_comp]
    have hal : Aligned (Drawing.transform f d).tip (join (f.comp g)) ↔
        Aligned d.tip (join g) := by
      simp only [Aligned,Drawing.transform_tip,join_comp,f.injective.eq_iff]
    rw [hal,separated_transform_iff]
    have hi : d.points.image f.map ∩ (strip g n).image f.map =
        {join (f.comp g) 0,join (f.comp g) 1} ↔
        d.points ∩ strip g n={join g 0,join g 1} := by
      rw [← Finset.image_inter _ _ f.injective,join_comp,join_comp]
      have hp : ({join g 0,join g 1} : Finset Point).image f.map =
          {f.map (join g 0),f.map (join g 1)} := by simp
      rw [← hp]
      exact Finset.image_injective f.injective |>.eq_iff
    rw [hi]

theorem Drawing.transform_valid (f : Frame) (d : Drawing) (h : d.Valid) :
    (Drawing.transform f d).Valid := (Drawing.transform_valid_iff f d).mpr h

end GridHardness.SignedTentacle
