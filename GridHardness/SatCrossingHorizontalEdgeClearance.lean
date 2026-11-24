/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingHorizontalRouting

/-!
# SAT Crossing Horizontal Edge Clearance

Horizontal connectors meet the routed internal edges of their two cells
only at their prescribed incident ports. The old cell contributes only edges
whose two endpoints survive removal of section zero.
-/

@[expose] public section

namespace GridHardness.SatCrossingHorizontal
open CliffordSynthesis PermutationWireLayout SatCrossingLattice
set_option autoImplicit false

/-- Both endpoints of an internal edge survive the next refinement. -/
def RetainedEdge (e : Fin 66) : Prop :=
  Retained (XorLine.Lattice.edge e).1 ∧ Retained (XorLine.Lattice.edge e).2

instance (e : Fin 66) : Decidable (RetainedEdge e) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
/-- Retained routes, including every intermediate lattice point, lie on the
retained side of the old row-zero ports. -/
theorem retained_route_local_bound : ∀ e : Fin 66, RetainedEdge e →
    ∀ q ∈ XorLine.Lattice.edgeRoute e, 20 ≤ q.2 := by decide +kernel

variable {n : Nat} (p : Equiv.Perm (Fin n))

theorem retained_route_bound (c : Cell n) (e : Fin 66) (he : RetainedEdge e)
    (q : Point) (hq : q ∈ SatCrossingLattice.route p c e) :
    q.1 ≤ 512 * low c.1 + 45 := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  have hb := retained_route_local_bound e he r hr
  rw [frame_map]
  dsimp
  omega

/-- An upper connector can meet a retained old edge only at its old port;
the edge must actually be incident with that port. -/
theorem upper_old_edge_intersection (i k j : Fin n) (hik : i < k)
    (e : Fin 66) (he : RetainedEdge e) (q : Point) :
    (q ∈ upperRoute p i k j ∧ q ∈ SatCrossingLattice.route p (i,j) e) ↔
      q = point p (i,j) (XorLine.row 0 false) ∧
        (XorLine.row 0 false = (XorLine.Lattice.edge e).1 ∨
          XorLine.row 0 false = (XorLine.Lattice.edge e).2) := by
  constructor
  · rintro ⟨hq, ht⟩
    have hx := retained_route_bound p (i,j) e he q ht
    have hp := upperPath_left _ _ _ (gapLength_pos i k hik) q hq hx
    rw [← (row_zero_coordinates p (i,j)).1] at hp
    refine ⟨hp, ?_⟩
    rw [hp] at ht
    exact (SatCrossingLattice.route_vertex_clear p (i,j) e (XorLine.row 0 false)).mp ht
  · rintro ⟨rfl, he⟩
    exact ⟨List.mem_of_head? (route_endpoints p i k j hik).1,
      (SatCrossingLattice.route_vertex_clear p (i,j) e (XorLine.row 0 false)).mpr he⟩

theorem lower_old_edge_intersection (i k j : Fin n) (hik : i < k)
    (e : Fin 66) (he : RetainedEdge e) (q : Point) :
    (q ∈ lowerRoute p i k j ∧ q ∈ SatCrossingLattice.route p (i,j) e) ↔
      q = point p (i,j) (XorLine.row 0 true) ∧
        (XorLine.row 0 true = (XorLine.Lattice.edge e).1 ∨
          XorLine.row 0 true = (XorLine.Lattice.edge e).2) := by
  constructor
  · rintro ⟨hq, ht⟩
    have hx := retained_route_bound p (i,j) e he q ht
    have hp := lowerPath_left _ _ _ (gapLength_pos i k hik) q hq hx
    rw [← (row_zero_coordinates p (i,j)).2] at hp
    refine ⟨hp, ?_⟩
    rw [hp] at ht
    exact (SatCrossingLattice.route_vertex_clear p (i,j) e (XorLine.row 0 true)).mp ht
  · rintro ⟨rfl, he⟩
    exact ⟨List.mem_of_getLast? (route_endpoints p i k j hik).2.2.2,
      (SatCrossingLattice.route_vertex_clear p (i,j) e (XorLine.row 0 true)).mpr he⟩

/-- At the new cell, the entire routed edge stays in the box, so the upper
connector can touch it only at the false input port. -/
theorem upper_new_edge_intersection (i k j : Fin n) (hik : i < k)
    (e : Fin 66) (q : Point) :
    (q ∈ upperRoute p i k j ∧ q ∈ SatCrossingLattice.route p (k,j) e) ↔
      q = point p (k,j) (XorLine.inputPort 4 (.inl false)) ∧
        (XorLine.inputPort 4 (.inl false) = (XorLine.Lattice.edge e).1 ∨
          XorLine.inputPort 4 (.inl false) = (XorLine.Lattice.edge e).2) := by
  constructor
  · rintro ⟨hq, ht⟩
    have hb := SatCrossingLattice.route_in_box p (k,j) e q ht
    have hg := gapLength_cast i k hik
    have hx : 512 * low i + 45 + (gapLength i k : Int) + 10 ≤ q.1 := by
      dsimp [InBox] at hb
      omega
    have hp := upperPath_right _ _ _ q hq hx
    have he : 512 * low i + 45 + (gapLength i k : Int) + 10 = 512 * low k - 65 := by
      omega
    rw [he, ← (main_port_coordinates p (k,j)).2.2.1] at hp
    refine ⟨hp, ?_⟩
    rw [hp] at ht
    exact (SatCrossingLattice.route_vertex_clear p (k,j) e _).mp ht
  · rintro ⟨rfl, he⟩
    exact ⟨List.mem_of_getLast? (route_endpoints p i k j hik).2.1,
      (SatCrossingLattice.route_vertex_clear p (k,j) e _).mpr he⟩

theorem lower_new_edge_intersection (i k j : Fin n) (hik : i < k)
    (e : Fin 66) (q : Point) :
    (q ∈ lowerRoute p i k j ∧ q ∈ SatCrossingLattice.route p (k,j) e) ↔
      q = point p (k,j) (XorLine.outputPort 4 (.inl false)) ∧
        (XorLine.outputPort 4 (.inl false) = (XorLine.Lattice.edge e).1 ∨
          XorLine.outputPort 4 (.inl false) = (XorLine.Lattice.edge e).2) := by
  constructor
  · rintro ⟨hq, ht⟩
    have hb := SatCrossingLattice.route_in_box p (k,j) e q ht
    have hg := gapLength_cast i k hik
    have hx : 512 * low i + 45 + (gapLength i k : Int) + 10 ≤ q.1 := by
      dsimp [InBox] at hb
      omega
    have hp := lowerPath_right _ _ _ q hq hx
    have he : 512 * low i + 45 + (gapLength i k : Int) + 10 = 512 * low k - 65 := by
      omega
    rw [he, ← (main_port_coordinates p (k,j)).2.2.2] at hp
    refine ⟨hp, ?_⟩
    rw [hp] at ht
    exact (SatCrossingLattice.route_vertex_clear p (k,j) e _).mp ht
  · rintro ⟨rfl, he⟩
    exact ⟨List.mem_of_head? (route_endpoints p i k j hik).2.2.1,
      (SatCrossingLattice.route_vertex_clear p (k,j) e _).mpr he⟩

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
private theorem local_endpoints_not_interior : ∀ e : Fin 66,
    XorLine.Lattice.point (XorLine.Lattice.edge e).1 ∉ XorLine.Lattice.interior e ∧
      XorLine.Lattice.point (XorLine.Lattice.edge e).2 ∉ XorLine.Lattice.interior e := by
  decide +kernel

theorem route_endpoint_not_interior (c : Cell n) (e : Fin 66)
    (v : XorLine.Vertex 4)
    (hv : v = (XorLine.Lattice.edge e).1 ∨ v = (XorLine.Lattice.edge e).2) :
    point p c v ∉ (SatCrossingLattice.route p c e).tail.dropLast := by
  intro h
  change (frame p c).map (XorLine.Lattice.point v) ∈
    ((XorLine.Lattice.edgeRoute e).map (frame p c).map).tail.dropLast at h
  rw [← List.map_tail, ← List.map_dropLast,
    List.mem_map_of_injective (frame p c).injective] at h
  rcases hv with rfl | rfl
  · exact (local_endpoints_not_interior e).1 h
  · exact (local_endpoints_not_interior e).2 h

/-- The connectors avoid every interior point of every retained old edge. -/
theorem old_edge_interiors_disjoint (i k j : Fin n) (hik : i < k)
    (e : Fin 66) (he : RetainedEdge e) :
    (upperRoute p i k j).Disjoint (SatCrossingLattice.route p (i,j) e).tail.dropLast ∧
      (lowerRoute p i k j).Disjoint (SatCrossingLattice.route p (i,j) e).tail.dropLast := by
  constructor
  · apply List.disjoint_left.mpr
    intro q hq ht
    have hf := List.mem_of_mem_tail (List.mem_of_mem_dropLast ht)
    obtain ⟨hp, hv⟩ := (upper_old_edge_intersection p i k j hik e he q).mp ⟨hq, hf⟩
    rw [hp] at ht
    exact route_endpoint_not_interior p (i,j) e _ hv ht
  · apply List.disjoint_left.mpr
    intro q hq ht
    have hf := List.mem_of_mem_tail (List.mem_of_mem_dropLast ht)
    obtain ⟨hp, hv⟩ := (lower_old_edge_intersection p i k j hik e he q).mp ⟨hq, hf⟩
    rw [hp] at ht
    exact route_endpoint_not_interior p (i,j) e _ hv ht

/-- The connectors avoid every interior point of every new-cell edge. -/
theorem new_edge_interiors_disjoint (i k j : Fin n) (hik : i < k) (e : Fin 66) :
    (upperRoute p i k j).Disjoint (SatCrossingLattice.route p (k,j) e).tail.dropLast ∧
      (lowerRoute p i k j).Disjoint (SatCrossingLattice.route p (k,j) e).tail.dropLast := by
  constructor
  · apply List.disjoint_left.mpr
    intro q hq ht
    have hf := List.mem_of_mem_tail (List.mem_of_mem_dropLast ht)
    obtain ⟨hp, hv⟩ := (upper_new_edge_intersection p i k j hik e q).mp ⟨hq, hf⟩
    rw [hp] at ht
    exact route_endpoint_not_interior p (k,j) e _ hv ht
  · apply List.disjoint_left.mpr
    intro q hq ht
    have hf := List.mem_of_mem_tail (List.mem_of_mem_dropLast ht)
    obtain ⟨hp, hv⟩ := (lower_new_edge_intersection p i k j hik e q).mp ⟨hq, hf⟩
    rw [hp] at ht
    exact route_endpoint_not_interior p (k,j) e _ hv ht

end GridHardness.SatCrossingHorizontal
