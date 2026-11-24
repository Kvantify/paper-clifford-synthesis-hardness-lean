/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridPointCode
public import GridHardness.FrameComposition

/-!
# Grid Assembly Rectangles

Serialize concrete cluster/tentacle layouts as explicit padded rectangles.
This connects the coordinate geometry to the certified point-set compiler;
all strip enumeration is driven by actual padding lists.
-/

@[expose] public section

namespace GridHardness.GridAssembly.Rectangles
open CliffordSynthesis OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems.GridCode GridPointCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Padding lengths are rectangle side lengths (not signed coordinates). -/
def box (f : Frame) (w h : Nat) : RectangleTy.denote :=
  (encodeFrame f, (List.replicate w false, List.replicate h false))

theorem mem_box (f : Frame) (w h : Nat) (p : Point) :
    p ∈ rectanglePoints (box f w h) ↔
      0 ≤ (f.unmap p).1 ∧ (f.unmap p).1 < w ∧
      0 ≤ (f.unmap p).2 ∧ (f.unmap p).2 < h := by
  simp only [rectanglePoints, box, List.length_replicate, decode_encodeFrame]
  change p ∈ (((Finset.range w).product (Finset.range h)).image
    (fun q : Nat × Nat => f.map (q.1, q.2))) ↔ _
  constructor
  · intro hp
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hp
    have hi := Finset.mem_range.mp (Finset.mem_product.mp hij).1
    have hj := Finset.mem_range.mp (Finset.mem_product.mp hij).2
    rw [f.unmap_map]
    dsimp at hi hj ⊢
    omega
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨((f.unmap p).1.toNat, (f.unmap p).2.toNat),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩, ?_⟩
    have he : (((f.unmap p).1.toNat : Int), ((f.unmap p).2.toNat : Int)) = f.unmap p := by
      apply Prod.ext <;> dsimp <;> omega
    rw [he, f.map_unmap]

private theorem mem_image_iff (f : Frame) (S : Finset Point) (p : Point) :
    p ∈ S.image f.map ↔ f.unmap p ∈ S := by
  constructor
  · rintro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    simpa only [f.unmap_map] using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨f.unmap p, hp, f.map_unmap p⟩

@[simp] theorem box_strip (f : Frame) (n : Nat) :
    rectanglePoints (box f (n+1) 2) = strip f n := by
  ext p
  rw [mem_box, mem_strip_iff]
  omega

@[simp] theorem box_cluster (f : Frame) :
    rectanglePoints (box f 3 3) = NineClusterAttachment.points.image f.map := by
  ext p
  rw [mem_box, mem_image_iff, NineClusterAttachment.mem_points_iff]
  omega

@[simp] theorem points_nil : GridPointCode.points [] = ∅ := by simp [GridPointCode.points]

@[simp] theorem points_cons (r : RectangleTy.denote) (rs : GridPointCode.InputTy.denote) :
    GridPointCode.points (r :: rs) = rectanglePoints r ∪ GridPointCode.points rs := by
  simp [GridPointCode.points]

@[simp] theorem points_append (rs ts : GridPointCode.InputTy.denote) :
    GridPointCode.points (rs ++ ts) = GridPointCode.points rs ∪ GridPointCode.points ts := by
  simp [GridPointCode.points, Finset.union_biUnion]

@[simp] theorem strip_comp (f g : Frame) (n : Nat) :
    strip (f.comp g) n = (strip g n).image f.map := by
  exact f.image_comp g _

def drawing (f : Frame) : Drawing → GridPointCode.InputTy.denote
  | .base g n => [box (f.comp g) (n+1) 2]
  | .attach d g n => drawing f d ++ [box (f.comp g) (n+1) 2]

/-- Every segment of any signed drawing is included, with exact overlaps
and global placement preserved; no geometric validity hypothesis is needed. -/
@[simp] theorem drawing_points (f : Frame) (d : Drawing) :
    GridPointCode.points (drawing f d) = d.points.image f.map := by
  induction d with
  | base g n =>
    rw [drawing, points_cons, points_nil, box_strip, strip_comp, Finset.union_empty]
    rfl
  | attach d g n ih =>
    rw [drawing, points_append, points_cons, points_nil, box_strip, strip_comp,
      Finset.union_empty, ih, Drawing.points, Finset.image_union]

def arm (f : Frame) : Arm → GridPointCode.InputTy.denote
  | none => []
  | some (_, d) => drawing f d

@[simp] theorem arm_points (f : Frame) (a : Arm) :
    GridPointCode.points (arm f a) = (armPoints a).image f.map := by
  cases a with
  | none => rw [arm, points_nil, armPoints, Finset.image_empty]
  | some a => exact drawing_points f a.2

def arms (f : Frame) (a : Arms) : GridPointCode.InputTy.denote :=
  arm f (a 0) ++ arm f (a 1) ++ arm f (a 2)

@[simp] theorem arms_points (f : Frame) (a : Arms) :
    GridPointCode.points (arms f a) =
      (Finset.univ.biUnion (fun i => armPoints (a i))).image f.map := by
  have he : Finset.univ.biUnion (fun i : Fin 3 => armPoints (a i)) =
      armPoints (a 0) ∪ armPoints (a 1) ∪ armPoints (a 2) := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((hp | hp) | hp)
      · exact ⟨0, hp⟩
      · exact ⟨1, hp⟩
      · exact ⟨2, hp⟩
  rw [arms, points_append, points_append, arm_points, arm_points, arm_points,
    he, Finset.image_union, Finset.image_union]

def body : Body → GridPointCode.InputTy.denote
  | .cluster f => [box f 3 3]
  | .star f a => box f 3 3 :: arms f a

@[simp] theorem body_points (b : Body) : GridPointCode.points (body b) = b.points := by
  cases b with
  | cluster f => rw [body, points_cons, points_nil, box_cluster, Finset.union_empty]; rfl
  | star f a => rw [body, points_cons, box_cluster, arms_points]; exact (Finset.image_union _ _).symm

/-- Explicit label order avoids any classical choice in serialization. -/
def layout {n : Nat} (l : Layout (Fin n)) : GridPointCode.InputTy.denote :=
  (List.ofFn (fun c => body (l.body c))).flatten

@[simp] theorem layout_points {n : Nat} (l : Layout (Fin n)) :
    GridPointCode.points (layout l) = l.points := by
  ext p
  simp only [GridPointCode.points, Finset.mem_biUnion, List.mem_toFinset,
    layout, List.mem_flatten, List.mem_ofFn]
  constructor
  · rintro ⟨r, ⟨rs, ⟨c, rfl⟩, hr⟩, hp⟩
    apply (l.mem_points p).mpr
    refine ⟨c, ?_⟩
    change p ∈ (l.body c).points
    rw [← body_points]
    exact Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr hr, hp⟩
  · intro hp
    obtain ⟨c, hc⟩ := (l.mem_points p).mp hp
    change p ∈ (l.body c).points at hc
    rw [← body_points] at hc
    obtain ⟨r, hr, hp⟩ := Finset.mem_biUnion.mp hc
    exact ⟨r, ⟨body (l.body c), ⟨c, rfl⟩, List.mem_toFinset.mp hr⟩, hp⟩

end GridHardness.GridAssembly.Rectangles
