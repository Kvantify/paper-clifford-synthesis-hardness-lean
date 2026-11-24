/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRetirementEmpty

/-!
# SAT Crossing Retirement Clearance

Clearance of final residual tails from the internal routes of the forty
vertices retained at each crossing. Only routes whose endpoints are retained
vertices are included.
-/

public section

namespace GridHardness.SatCrossingRetirement.Segments
open CliffordSynthesis PermutationWireLayout SatCrossingLattice
set_option autoImplicit false

private theorem local_retained_route_bound : ∀ e : Fin 66,
    SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).1 →
    SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).2 →
    ∀ q∈XorLine.Lattice.edgeRoute e, 20≤q.2 := by decide +kernel

variable {n : Nat} (p : Equiv.Perm (Fin n))

theorem retained_route_bound (d : Cell n) (e : Fin 66)
    (hs : SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).1)
    (ht : SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).2)
    (q : Point) (hq : q ∈SatCrossingLattice.route p d e) : q.1≤512*low d.1+45 := by
  obtain ⟨t,htq,rfl⟩ := List.mem_map.mp hq
  have hh := local_retained_route_bound e hs ht t htq
  rw [SatCrossingLattice.frame_map]
  dsimp
  omega

/-- The upper tail is disjoint from all internal routes of its last
horizontal tile that survive removal of section zero. -/
theorem upper_latest_route_clear (a i j : Fin n) (hai : a < i)
    (hij : SatCrossingRouting.Active p i j) (r : Fin 4) (e : Fin 66)
    (hs : SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).1)
    (ht : SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).2) :
    (upper p (some a) i j r).Disjoint (SatCrossingLattice.route p (a,i) e) := by
  apply List.disjoint_left.mpr
  intro q hq hqe
  have hm := (upper_mem p (some a) i j (by intro k hk; cases hk; exact hai) hij r _).mp hq
  have hb := retained_route_bound p (a,i) e hs ht q hqe
  dsimp only [Prod.fst] at hb
  have hh := low_lt_low hai
  have hr := r.isLt
  dsimp [Placement.left,SatCrossingRouting.lane] at hm
  rcases hm with hm | hm <;> omega

/-- Any intersection between an upper tail and a retained cell-internal
route is exactly its designated row port in the highest crossing cell. -/
theorem upper_retained_route_clear (last : Option (Fin n)) (i j : Fin n)
    (hl : LastInRow p last i) (hj : LastInColumn p i j)
    (r : Fin 4) (d : Cell n) (hd : SatCrossingRouting.Active p d.1 d.2)
    (e : Fin 66) (hs : SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).1)
    (ht : SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).2)
    (q : Point) (hq : q ∈upper p last i j r) (he : q ∈SatCrossingLattice.route p d e) :
    d=(i,j) ∧ q=point p (i,j) (SatCrossingRouting.lowerPort r) := by
  have hl' := lastInRow_before p last i hl
  by_cases hdj : d=(i,j)
  · subst d
    have h := (upper_endpoint_box p last i j hl' hj.1 r q hq).mp (route_in_box p _ e q he)
    rw [SatCrossingRouting.lowerPort_coordinates]
    exact ⟨rfl,h⟩
  · by_cases hh : last=some d.1 ∧ d.2=i
    · obtain ⟨hh,hi⟩ := hh
      have hdi := hl' d.1 hh
      change q∈SatCrossingLattice.route p (d.1,d.2) e at he
      rw [hh] at hq
      rw [hi] at he
      exact False.elim (List.disjoint_left.mp (upper_latest_route_clear p d.1 i j hdi hj.1 r e hs ht) hq he)
    · have hh' : last≠some d.1 ∨ d.2≠i := by tauto
      exact False.elim (upper_other_box_clear p last i j hl hj r d hd hdj hh' q hq
        (route_in_box p d e q he))

/-- A lower tail touches a local internal route only at its designated row
port in the lowest crossing cell. -/
theorem lower_route_clear (last : Option (Fin n)) (i j : Fin n)
    (hl : Placement.LastBefore last i) (hj : FirstInColumn p i j)
    (r : Fin 4) (d : Cell n) (hd : SatCrossingRouting.Active p d.1 d.2)
    (e : Fin 66) (q : Point) (hq : q ∈lower p last i j r)
    (he : q ∈SatCrossingLattice.route p d e) :
    d=(i,j) ∧ q=point p (i,j) (SatCrossingRouting.upperPort r) := by
  rw [SatCrossingRouting.upperPort_coordinates]
  exact lower_box_clear p last i j hl hj r d hd q hq (route_in_box p d e q he)

theorem whole_latest_route_clear (a i : Fin n) (hai : a < i) (r : Fin 4) (e : Fin 66)
    (hs : SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).1)
    (ht : SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).2) :
    (Placement.route p (some a) i r).Disjoint (SatCrossingLattice.route p (a,i) e) := by
  apply List.disjoint_left.mpr
  intro q hq hqe
  have hm := (whole_mem p (some a) i (by intro k hk; cases hk; exact hai) r q).mp hq
  have hb := retained_route_bound p (a,i) e hs ht q hqe
  dsimp only [Prod.fst] at hb
  have hh := low_lt_low hai
  have hr := r.isLt
  dsimp [Placement.left,SatCrossingRouting.lane] at hm
  rcases hm with hm | hm | hm <;> omega

/-- If no crossing cuts the retired lane, its entire route is disjoint from
the retained internal drawing of every active crossing cell. -/
theorem whole_retained_route_clear (last : Option (Fin n)) (i : Fin n)
    (hl : LastInRow p last i) (he : EmptyColumn p i) (r : Fin 4)
    (d : Cell n) (hd : SatCrossingRouting.Active p d.1 d.2)
    (e : Fin 66) (hs : SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).1)
    (ht : SatCrossingHorizontal.Retained (XorLine.Lattice.edge e).2) :
    (Placement.route p last i r).Disjoint (SatCrossingLattice.route p d e) := by
  apply List.disjoint_left.mpr
  intro q hq hqe
  by_cases hh : last=some d.1 ∧ d.2=i
  · obtain ⟨hh,hi⟩ := hh
    have hdi := lastInRow_before p last i hl d.1 hh
    change q∈SatCrossingLattice.route p (d.1,d.2) e at hqe
    rw [hh] at hq
    rw [hi] at hqe
    exact List.disjoint_left.mp (whole_latest_route_clear p d.1 i hdi r e hs ht) hq hqe
  · have hh' : last≠some d.1 ∨ d.2≠i := by tauto
    exact whole_other_box_clear p last i hl he r d hd hh' q hq (route_in_box p d e q hqe)

end GridHardness.SatCrossingRetirement.Segments
