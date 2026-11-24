/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRetirementClearance

/-!
# SAT Crossing Retirement Links

The two local links retained between row zero and the false side of a
retired XOR. Their old lattice routes remain valid because retirement leaves
all four false-side vertices in place.
-/

@[expose] public section

namespace GridHardness.SatCrossingRetirement.Links
open CliffordSynthesis PermutationWireLayout SatCrossingLattice
open XorLine SatCrossingHorizontal Segments
set_option autoImplicit false

/-- One endpoint is a false-side vertex of section zero, and the other is
one of the forty retained vertices of the crossing cell. -/
def LinkEdge (e : Fin 66) : Prop :=
  (∃ r : Fin 4, Retained (XorLine.Lattice.edge e).1 ∧
    (XorLine.Lattice.edge e).2=x 0 (falseVertex r)) ∨
  (∃ r : Fin 4, (XorLine.Lattice.edge e).1=x 0 (falseVertex r) ∧
    Retained (XorLine.Lattice.edge e).2)

instance (e : Fin 66) : Decidable (LinkEdge e) := inferInstanceAs (Decidable (_ ∨ _))

/-- The adjacency interface proves that precisely two such links exist. -/
theorem linkEdge_iff (e : Fin 66) : LinkEdge e ↔
    XorLine.Lattice.edge e=(row 0 false,x 0 4) ∨
    XorLine.Lattice.edge e=(x 0 7,row 0 true) := by
  constructor
  · rintro (⟨r,hr,he⟩ | ⟨r,he,hr⟩)
    · have ha := XorLine.Lattice.edge_adj e
      rw [he] at ha
      have hi := (retained_enter _ hr (falseVertex r)).mp ha
      exact Or.inl (Prod.ext hi.1 (he.trans (congrArg (x 0) hi.2)))
    · have ha := XorLine.Lattice.edge_adj e
      rw [he] at ha
      have hi := (retained_leave _ hr (falseVertex r)).mp ha
      exact Or.inr (Prod.ext (he.trans (congrArg (x 0) hi.2)) hi.1)
  · intro h
    rcases h with h | h
    · apply Or.inl
      refine ⟨0,?_,?_⟩ <;> rw [h]
      · trivial
      · rfl
    · apply Or.inr
      refine ⟨3,?_,?_⟩ <;> rw [h]
      · rfl
      · trivial

private theorem link_indices : ∀ e : Fin 66,
    (XorLine.Lattice.edge e=(row 0 false,x 0 4) ∨
    XorLine.Lattice.edge e=(x 0 7,row 0 true)) ↔ e=50 ∨ e=52 := by decide +kernel

theorem linkEdge_iff_index (e : Fin 66) : LinkEdge e ↔ e=50 ∨ e=52 :=
  (linkEdge_iff e).trans (link_indices e)

private theorem local_link_bound : ∀ e : Fin 66, (e=50 ∨ e=52) →
    ∀ q∈XorLine.Lattice.edgeRoute e, 10≤q.2 ∧ q.2≤20 := by decide +kernel

variable {n : Nat} (p : Equiv.Perm (Fin n))

/-- Both old link routes stay on the retained side of the false endpoint
column. Their shapes and directions are unchanged by retirement. -/
theorem link_bounds (a i : Fin n) (e : Fin 66) (he : LinkEdge e)
    (q : Point) (hq : q ∈SatCrossingLattice.route p (a, i) e) :
    512*low a+45≤q.1 ∧ q.1≤512*low a+55 := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hq
  have hh := local_link_bound e ((linkEdge_iff_index e).mp he) t ht
  rw [SatCrossingLattice.frame_map]
  dsimp
  omega

/-- Directed endpoints of the incoming link, using the actual relocated-XOR
placement for its false endpoint. -/
theorem incoming_endpoints (a i : Fin n) (hai : a < i) :
    (SatCrossingLattice.route p (a,i) 50).head?=some (point p (a,i) (row 0 false)) ∧
    (SatCrossingLattice.route p (a,i) 50).getLast?=some (Placement.point p (some a) i (falseVertex 0)) := by
  have hc := SatCrossingLattice.route_certificate p (a,i) 50
  have he : XorLine.Lattice.edge 50=(row 0 false,x 0 (falseVertex 0)) := by decide +kernel
  rw [he] at hc
  rw [Placement.latest_false_unchanged p a i hai 0]
  exact ⟨hc.1,hc.2.1⟩

theorem outgoing_endpoints (a i : Fin n) (hai : a < i) :
    (SatCrossingLattice.route p (a,i) 52).head?=some (Placement.point p (some a) i (falseVertex 3)) ∧
    (SatCrossingLattice.route p (a,i) 52).getLast?=some (point p (a,i) (row 0 true)) := by
  have hc := SatCrossingLattice.route_certificate p (a,i) 52
  have he : XorLine.Lattice.edge 52=(x 0 (falseVertex 3),row 0 true) := by decide +kernel
  rw [he] at hc
  rw [Placement.latest_false_unchanged p a i hai 3]
  exact ⟨hc.1,hc.2.1⟩

/-- A point of a complete mandatory route at or left of its false endpoint
column must be the false endpoint itself. -/
theorem whole_left_boundary (a i : Fin n) (hai : a < i) (r : Fin 4)
    (q : Point) (hq : q ∈Placement.route p (some a) i r)
    (hx : q.1 ≤512 *low a +55) : q=Placement.point p (some a) i (falseVertex r) := by
  have hl : Placement.LastBefore (some a) i := by intro k hk; cases hk; exact hai
  have hm := (whole_mem p (some a) i hl r q).mp hq
  have hh := low_lt_low hai
  have hr := r.isLt
  rw [Placement.false_coordinates p (some a) i hl r]
  dsimp [Placement.left,SatCrossingRouting.lane] at hm ⊢
  rcases hm with hm | hm | hm
  · exact Prod.ext (by omega) hm.1
  · omega
  · omega

/-- A surviving local link meets a complete mandatory retirement route only
at a shared false-side XOR endpoint. -/
theorem whole_link_intersection (a i : Fin n) (hai : a < i) (r : Fin 4)
    (e : Fin 66) (he : LinkEdge e) (q : Point)
    (hq : q ∈Placement.route p (some a) i r) (hqe : q ∈SatCrossingLattice.route p (a, i) e) :
    q=Placement.point p (some a) i (falseVertex r) ∧
      (x 0 (falseVertex r)=(XorLine.Lattice.edge e).1 ∨
       x 0 (falseVertex r)=(XorLine.Lattice.edge e).2) := by
  have hb := (link_bounds p a i e he q hqe).2
  have hp := whole_left_boundary p a i hai r q hq hb
  refine ⟨hp,?_⟩
  rw [hp,Placement.latest_false_unchanged p a i hai r] at hqe
  exact (SatCrossingLattice.route_vertex_clear p (a,i) e (x 0 (falseVertex r))).mp hqe

theorem upper_link_intersection (a i j : Fin n) (hai : a < i)
    (hij : SatCrossingRouting.Active p i j) (r : Fin 4)
    (e : Fin 66) (he : LinkEdge e) (q : Point)
    (hq : q ∈upper p (some a) i j r) (hqe : q ∈SatCrossingLattice.route p (a, i) e) :
    q=Placement.point p (some a) i (falseVertex r) ∧
      (x 0 (falseVertex r)=(XorLine.Lattice.edge e).1 ∨
       x 0 (falseVertex r)=(XorLine.Lattice.edge e).2) := by
  have hl : Placement.LastBefore (some a) i := by intro k hk; cases hk; exact hai
  exact whole_link_intersection p a i hai r e he q (upper_subset p (some a) i j hl hij r hq) hqe

/-- Lower residual tails lie strictly to the right of both local links. -/
theorem lower_links_disjoint (a i j : Fin n) (hai : a < i)
    (hij : SatCrossingRouting.Active p i j) (r : Fin 4)
    (e : Fin 66) (he : LinkEdge e) :
    (lower p (some a) i j r).Disjoint (SatCrossingLattice.route p (a,i) e) := by
  apply List.disjoint_left.mpr
  intro q hq hqe
  have hl : Placement.LastBefore (some a) i := by intro k hk; cases hk; exact hai
  have hm := (lower_mem p (some a) i j hl hij r q).mp hq
  have hb := (link_bounds p a i e he q hqe).2
  have hh := low_lt_low hai
  have hr := r.isLt
  dsimp [SatCrossingRouting.lane] at hm
  rcases hm with hm | hm <;> omega

end GridHardness.SatCrossingRetirement.Links
