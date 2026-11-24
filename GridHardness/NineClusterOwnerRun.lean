/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacleDrawingFrom
public import GridHardness.SignedTentacleEndpointLocality
public import GridHardness.NineClusterDockGeometry
public import GridHardness.NineClusterPlacement

/-!
# Nine Cluster Owner Run

Initialize the cardinal strip compiler at the two-edge owner dock.
Lane one is the radial ideal centerline, while lane zero is the prescribed
corner port. Endpoint localization proves the exact two-edge boundary.
-/

@[expose] public section

namespace GridHardness.NineClusterOwnerRun
open CliffordSynthesis OrthogonalTentacle SignedTentacle SignedTentacle.CardinalRunChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q = 1))

def state (f : Frame) (side : Fin 4) : RunState :=
  ⟨f.comp (NineClusterAttachment.dock true side), 0, 1⟩

def drawing (f : Frame) (side : Fin 4) (length : Nat) (rs : List Run) : Drawing :=
  drawingFrom (state f side) length rs

@[simp] theorem state_length (f : Frame) (side : Fin 4) (length : Nat) :
    (state f side).length length = length := by
  simp [state, RunState.length, runLength]

theorem state_point_zero (f : Frame) (side : Fin 4) :
    (state f side).point 0 = f.map (near (NineClusterAttachment.dock true side) 1) := by
  simp [state, RunState.point, runPoint, near, Frame.map_comp]

/-- The radial lane begins two steps from the cluster center. -/
theorem state_start_distance (f : Frame) (side : Fin 4) :
    IntegerGrid.manhattan (f.map (1, 1)) ((state f side).point 0) = 2 := by
  rw [state_point_zero, f.distance]
  fin_cases side <;>
    norm_num [NineClusterAttachment.dock, near, Frame.map, place, sign, IntegerGrid.manhattan]

theorem state_direction (scale : Nat) (p : Point) (phase : Fin 2) (side : Fin 4) :
    (state (NineClusterPlacement.frame scale p phase) side).frame.axisDirection =
      NineClusterDockGeometry.directionOfSide side := by
  fin_cases side <;> rfl

/-- For the color-zero placement, the radial ideal start is exactly
the scaled graph anchor plus two steps in the incidence direction. -/
theorem state_owner_start (scale : Nat) (p : Point) (side : Fin 4) :
    (state (NineClusterPlacement.frame scale p 0) side).point 0 =
      LatticeRouteRuns.advance (LatticeSubdivision.scale scale p)
        (NineClusterDockGeometry.directionOfSide side) 2 := by
  rw [state_point_zero]
  fin_cases side <;>
    simp [NineClusterPlacement.frame, NineClusterAttachment.dock, near,
      Frame.map, place, sign, LatticeRouteRuns.advance, LatticeSubdivision.scale,
      NineClusterDockGeometry.directionOfSide, DirectedLocalLayout.ray] <;> omega

theorem drawing_start (f : Frame) (side : Fin 4) (length : Nat) (rs : List Run)
    (r : Fin 2) :
    (drawing f side length rs).start r =
      f.map (near (NineClusterAttachment.dock true side) r) := by
  rw [drawing, drawingFrom_start]
  exact near_comp f _ r

theorem drawing_ideal_start (f : Frame) (side : Fin 4) (length : Nat) (rs : List Run) :
    (drawing f side length rs).start 1 = (state f side).point 0 :=
  drawingFrom_ideal_start _ _ _ rfl

theorem drawing_firstStrip (f : Frame) (side : Fin 4) (length : Nat) (rs : List Run)
    (p : Point) (hp : p ∈ strip (state f side).frame length) :
    p ∈ (drawing f side length rs).points := by
  exact drawingFrom_firstStrip_mem _ _ _ _ (by simpa only [state_length] using hp)

theorem cluster_center_distance (f : Frame) (p : Point)
    (hp : p ∈ TwoClusterAssembly.cluster f) :
    IntegerGrid.manhattan (f.map (1, 1)) p ≤ 2 := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  rw [f.distance]
  have h := (NineClusterAttachment.mem_points_iff q).mp hq
  dsimp [IntegerGrid.manhattan]
  omega

private theorem local_of_center (f : Frame) (side : Fin 4) (q : Point)
    (hq : IntegerGrid.manhattan (f.map (1, 1)) q ≤ 3) :
    IntegerGrid.manhattan ((state f side).point 0) q ≤ 5 := by
  have hs := state_start_distance f side
  have ht := IntegerGrid.manhattan_triangle ((state f side).point 0) (f.map (1, 1)) q
  rw [IntegerGrid.manhattan_comm ((state f side).point 0) (f.map (1, 1))] at ht
  omega

/-- Localization of points near the ideal start prevents the drawing
from meeting its owner cluster. This is a finite geometric premise. -/
theorem disjoint_of_start_locality (f : Frame) (side : Fin 4) (length : Nat) (d : Drawing)
    (hloc : ∀ q ∈ d.points, IntegerGrid.manhattan ((state f side).point 0) q ≤ 5 →
      q ∈ strip (state f side).frame length) :
    Disjoint (TwoClusterAssembly.cluster f) d.points := by
  apply Finset.disjoint_left.mpr
  intro p hp hd
  have hc := cluster_center_distance f p hp
  have hs := hloc p hd (local_of_center f side p (by omega))
  change p ∈ strip (f.comp (NineClusterAttachment.dock true side)) length at hs
  rw [strip_comp] at hs
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hp
  obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hs
  have huv : u = v := f.injective (he.trans hve.symm)
  subst v
  exact Finset.disjoint_left.mp (NineClusterAttachment.dock_disjoint true side length) hu hv

theorem frame_dock_boundary (f : Frame) (side : Fin 4) (length : Nat)
    (c t : Point) (hc : c ∈ TwoClusterAssembly.cluster f)
    (ht : t ∈ strip (f.comp (NineClusterAttachment.dock true side)) length) :
    lattice.Adj c t ↔
      (c = TwoClusterAssembly.corner f side ∧
        t = f.map (near (NineClusterAttachment.dock true side) 0)) ∨
      (c = TwoClusterAssembly.mate f side ∧
        t = f.map (near (NineClusterAttachment.dock true side) 1)) := by
  rw [strip_comp] at ht
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
  rw [f.adj_iff]
  simpa only [TwoClusterAssembly.corner, TwoClusterAssembly.mate,
    f.injective.eq_iff, true_and] using NineClusterAttachment.dock_boundary true side length hu hv

/-- Only the corner edge and its reserved mate edge meet a localized
owner-initialized drawing, in the actual induced lattice graph. -/
theorem boundary_of_start_locality (f : Frame) (side : Fin 4) (length : Nat) (d : Drawing)
    (hstart : ∀ r : Fin 2, d.start r = f.map (near (NineClusterAttachment.dock true side) r))
    (hloc : ∀ q ∈ d.points, IntegerGrid.manhattan ((state f side).point 0) q ≤ 5 →
      q ∈ strip (state f side).frame length)
    (c t : Point) (hc : c ∈ TwoClusterAssembly.cluster f) (ht : t ∈ d.points) :
    lattice.Adj c t ↔
      (c = TwoClusterAssembly.corner f side ∧ t = d.start 0) ∨
      (c = TwoClusterAssembly.mate f side ∧ t = d.start 1) := by
  constructor
  · intro ha
    have hdist := cluster_center_distance f c hc
    have htri := IntegerGrid.manhattan_triangle (f.map (1, 1)) c t
    have hunit : IntegerGrid.manhattan c t = 1 := ha
    have hfirst := hloc t ht (local_of_center f side t (by omega))
    change t ∈ strip (f.comp (NineClusterAttachment.dock true side)) length at hfirst
    have hb := (frame_dock_boundary f side length c t hc hfirst).mp ha
    simpa only [← hstart 0, ← hstart 1] using hb
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [hstart]
      exact f.hom.map_adj (NineClusterAttachment.dock_first_adjacent true side)
    · rw [hstart]
      exact f.hom.map_adj (NineClusterAttachment.dock_second_adjacent side)

theorem boundary_eq_pair {S T : Finset Point} {a b c d : Point}
    (ha : a ∈ S) (hb : b ∈ T) (hc : c ∈ S) (hd : d ∈ T)
    (h : ∀ x ∈ S, ∀ y ∈ T, lattice.Adj x y ↔
      (x = a ∧ y = b) ∨ (x = c ∧ y = d)) :
    TwoClusterAssembly.boundary S T = {(a, b), (c, d)} := by
  apply Finset.ext
  intro e
  constructor
  · intro he
    have hf := Finset.mem_filter.mp he
    have hp := Finset.mem_product.mp hf.1
    rcases (h e.1 hp.1 e.2 hp.2).mp hf.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Finset.mem_insert.mpr (Or.inl (Prod.ext h0 h1))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Prod.ext h0 h1)))
  · intro he
    rcases Finset.mem_insert.mp he with he | he
    · subst e
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩,
        (h a ha b hb).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    · have he' := Finset.mem_singleton.mp he
      subst e
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc, hd⟩,
        (h c hc d hd).mpr (Or.inr ⟨rfl, rfl⟩)⟩

set_option backward.isDefEq.respectTransparency true in
theorem boundary_edges_of_start_locality (f : Frame) (side : Fin 4) (length : Nat) (d : Drawing)
    (hstart : ∀ r : Fin 2, d.start r = f.map (near (NineClusterAttachment.dock true side) r))
    (hfirst : ∀ q ∈ strip (state f side).frame length, q ∈ d.points)
    (hloc : ∀ q ∈ d.points, IntegerGrid.manhattan ((state f side).point 0) q ≤ 5 →
      q ∈ strip (state f side).frame length) :
    TwoClusterAssembly.boundary (TwoClusterAssembly.cluster f) d.points =
      {(TwoClusterAssembly.corner f side, d.start 0),
       (TwoClusterAssembly.mate f side, d.start 1)} := by
  have hmem (r : Fin 2) : d.start r ∈ d.points := by
    apply hfirst
    rw [hstart]
    change f.map (near (NineClusterAttachment.dock true side) r) ∈
      strip (f.comp (NineClusterAttachment.dock true side)) length
    rw [strip_comp, f.map_mem_image]
    exact near_mem _ _ _
  apply boundary_eq_pair (TwoClusterAssembly.corner_mem f side) (hmem 0)
    (TwoClusterAssembly.mate_mem f side) (hmem 1)
  intro c hc t ht
  exact boundary_of_start_locality f side length d hstart hloc c t hc ht

/-- Quantitative route separation discharges the owner boundary premise.
No global docking predicate or absence of unintended edges is assumed. -/
theorem drawing_owner_interface (f : Frame) (side : Fin 4) (length : Nat) (rs : List Run)
    (scale lower : Nat) (hmargin : 7 < min scale lower)
    (hc : ((state f side).frame.axisDirection::rs.map Prod.fst).IsChain
      (fun d e => d.val % 2 ≠ e.val % 2))
    (hs : LatticeRouteCore.IndexSeparated scale
      (LatticeRouteRuns.expandRuns ((state f side).point 0)
        (((state f side).frame.axisDirection, length)::rs)))
    (hn : ∀ r ∈ ((state f side).frame.axisDirection, length)::rs, lower ≤ r.2) :
    Disjoint (TwoClusterAssembly.cluster f) (drawing f side length rs).points ∧
      TwoClusterAssembly.boundary (TwoClusterAssembly.cluster f) (drawing f side length rs).points =
        {(TwoClusterAssembly.corner f side, (drawing f side length rs).start 0),
         (TwoClusterAssembly.mate f side, (drawing f side length rs).start 1)} := by
  have hloc : ∀ q ∈ (drawing f side length rs).points,
      IntegerGrid.manhattan ((state f side).point 0) q ≤ 5 →
      q ∈ strip (state f side).frame length := by
    intro q hq hqdist
    simpa only [state_length] using
      compile_first_strip_of_close (state f side) length rs scale lower hc hs hn q hq (by omega)
  exact ⟨disjoint_of_start_locality f side length _ hloc,
    boundary_edges_of_start_locality f side length _ (drawing_start f side length rs)
      (drawing_firstStrip f side length rs) hloc⟩

end GridHardness.NineClusterOwnerRun
