/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingHorizontalEdgeClearance

/-!
# SAT Crossing Vertical Edge Clearance

Exact intersections between vertical connectors and the routed edges of
all active crossing cells. The only intersections are the prescribed row
ports, and the local edge must be incident with that port.
-/

public section

namespace GridHardness.SatCrossingRouting
open SatCrossingLattice
set_option autoImplicit false

variable {n : Nat} (p : Equiv.Perm (Fin n))

theorem lower_edge_intersection (i j k : Fin n) (hc : Consecutive p i j k)
    (r : Fin 4) (e : Fin 66) (q : Point) :
    (q∈route p i j k r ∧ q∈SatCrossingLattice.route p (i,j) e) ↔
      q=point p (i,j) (lowerPort r) ∧
        (lowerPort r=(XorLine.Lattice.edge e).1 ∨ lowerPort r=(XorLine.Lattice.edge e).2) := by
  constructor
  · rintro ⟨hq,he⟩
    have hp := ((route_endpoint_boxes p i j k hc.2.2.1 r q hq).1).mp
      (route_in_box p (i,j) e q he)
    rw [← lowerPort_coordinates p i j r] at hp
    refine ⟨hp,?_⟩
    rw [hp] at he
    exact (SatCrossingLattice.route_vertex_clear p (i,j) e (lowerPort r)).mp he
  · rintro ⟨rfl,he⟩
    exact ⟨(route_vertex_clear p i j k hc r (i,j) hc.1 (lowerPort r)).mpr
      (Or.inl ⟨rfl,rfl⟩),
      (SatCrossingLattice.route_vertex_clear p (i,j) e (lowerPort r)).mpr he⟩

theorem upper_edge_intersection (i j k : Fin n) (hc : Consecutive p i j k)
    (r : Fin 4) (e : Fin 66) (q : Point) :
    (q∈route p i j k r ∧ q∈SatCrossingLattice.route p (i,k) e) ↔
      q=point p (i,k) (upperPort r) ∧
        (upperPort r=(XorLine.Lattice.edge e).1 ∨ upperPort r=(XorLine.Lattice.edge e).2) := by
  constructor
  · rintro ⟨hq,he⟩
    have hp := ((route_endpoint_boxes p i j k hc.2.2.1 r q hq).2).mp
      (route_in_box p (i,k) e q he)
    rw [← upperPort_coordinates p i k r] at hp
    refine ⟨hp,?_⟩
    rw [hp] at he
    exact (SatCrossingLattice.route_vertex_clear p (i,k) e (upperPort r)).mp he
  · rintro ⟨rfl,he⟩
    exact ⟨(route_vertex_clear p i j k hc r (i,k) hc.2.1 (upperPort r)).mpr
      (Or.inr ⟨rfl,rfl⟩),
      (SatCrossingLattice.route_vertex_clear p (i,k) e (upperPort r)).mpr he⟩

/-- The statement covers every routed edge of every active cell, including
cells in other columns and cells above or below this consecutive pair. -/
theorem edge_intersection_iff (i j k : Fin n) (hc : Consecutive p i j k)
    (r : Fin 4) (d : Cell n) (hd : Active p d.1 d.2) (e : Fin 66) (q : Point) :
    (q∈route p i j k r ∧ q∈SatCrossingLattice.route p d e) ↔
      (d=(i,j) ∧ q=point p (i,j) (lowerPort r) ∧
        (lowerPort r=(XorLine.Lattice.edge e).1 ∨ lowerPort r=(XorLine.Lattice.edge e).2)) ∨
      (d=(i,k) ∧ q=point p (i,k) (upperPort r) ∧
        (upperPort r=(XorLine.Lattice.edge e).1 ∨ upperPort r=(XorLine.Lattice.edge e).2)) := by
  constructor
  · rintro ⟨hq,he⟩
    by_cases hj : d=(i,j)
    · subst d
      exact Or.inl ⟨rfl,(lower_edge_intersection p i j k hc r e q).mp ⟨hq,he⟩⟩
    · by_cases hk : d=(i,k)
      · subst d
        exact Or.inr ⟨rfl,(upper_edge_intersection p i j k hc r e q).mp ⟨hq,he⟩⟩
      · exact False.elim (route_other_box_clear p i j k hc r d hd hj hk q hq
          (route_in_box p d e q he))
  · rintro (⟨rfl,hp,he⟩ | ⟨rfl,hp,he⟩)
    · exact (lower_edge_intersection p i j k hc r e q).mpr ⟨hp,he⟩
    · exact (upper_edge_intersection p i j k hc r e q).mpr ⟨hp,he⟩

theorem edge_interiors_disjoint (i j k : Fin n) (hc : Consecutive p i j k)
    (r : Fin 4) (d : Cell n) (hd : Active p d.1 d.2) (e : Fin 66) :
    (route p i j k r).Disjoint (SatCrossingLattice.route p d e).tail.dropLast := by
  apply List.disjoint_left.mpr
  intro q hq he
  have hf := List.mem_of_mem_tail (List.mem_of_mem_dropLast he)
  rcases (edge_intersection_iff p i j k hc r d hd e q).mp ⟨hq,hf⟩ with
    ⟨rfl,rfl,hv⟩ | ⟨rfl,rfl,hv⟩
  · exact SatCrossingHorizontal.route_endpoint_not_interior p (i,j) e _ hv he
  · exact SatCrossingHorizontal.route_endpoint_not_interior p (i,k) e _ hv he

end GridHardness.SatCrossingRouting
