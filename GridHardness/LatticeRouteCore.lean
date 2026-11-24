/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeEndpointNeighborhood
public import GridHardness.LatticeRouteTrim

/-!
# Lattice Route Core

Removing endpoint neighborhoods from dilated simple lattice routes.
The resulting corridor stays a specified distance from both endpoints;
unrelated original vertices retain the full dilation margin.
-/

@[expose] public section

namespace GridHardness.LatticeRouteCore
open CliffordSynthesis LatticeSubdivision
set_option autoImplicit false

/-- The parameter along a dilated unit edge is its distance from the source. -/
theorem interpolate_distance (s : Nat) {p q : Point} (h : UnitStep p q) (k : Nat) :
    IntegerGrid.manhattan (scale s p) (interpolate s p q k)=k := by
  rcases (manhattan_one_iff p q).mp h with rfl | rfl | rfl | rfl <;>
    simp [scale,interpolate,IntegerGrid.manhattan]

/-- Membership in a trimmed simple list bounds the original index. -/
theorem index_bounds {α : Type*} (a b : Nat) (l : List α) (hn : l.Nodup)
    (q : α) (hq : q ∈LatticeRouteTrim.trim a b l)
    (i : Nat) (hi : i <l.length) (he : q =l[i]) :
    a ≤ i ∧ i < l.length-b := by
  obtain ⟨j,hj,hjq⟩ := List.mem_iff_getElem.mp hq
  rw [LatticeRouteTrim.getElem] at hjq
  have hei : a+j=i := hn.getElem_inj_iff.mp (hjq.trans he)
  rw [LatticeRouteTrim.length] at hj
  omega

def core (s a b : Nat) (l : List Point) : List Point :=
  LatticeRouteTrim.trim a b (subdivide s l)

theorem mem_subdivide (s a b : Nat) (l : List Point) (q : Point)
    (hq : q ∈core s a b l) : q∈subdivide s l :=
  LatticeRouteTrim.mem a b _ q hq

/-- Trimming `a` initial points removes the open radius-`a` endpoint ball. -/
theorem initial_clearance (s a b : Nat) (hs : 0 <s) (ha : a ≤s)
    (l : List Point) (hn : l.Nodup) (hc : l.IsChain UnitStep) (hl : 2 ≤l.length)
    (q : Point) (hq : q ∈core s a b l) :
    a≤IntegerGrid.manhattan (scale s (l[0]'(by omega))) q := by
  by_contra h
  have hd : IntegerGrid.manhattan (scale s (l[0]'(by omega))) q<s := by omega
  obtain ⟨k,hk,he⟩ := getElem_initial_neighborhood s hs l hn hc hl q
    (mem_subdivide s a b l q hq) hd
  have hi := index_bounds a b (subdivide s l) (subdivide_nodup s l hn hc) q hq k _ he
  have he' := he.trans (subdivide_getElem_initial s l hl k hk)
  have hu : UnitStep (l[0]'(by omega)) (l[1]'(by omega)) := by
    cases l with
    | nil => simp at hl
    | cons p l =>
      cases l with
      | nil => simp at hl
      | cons r l => exact (List.isChain_cons_cons.mp hc).1
  have hm : IntegerGrid.manhattan (scale s (l[0]'(by omega))) q=k := by
    rw [he']
    exact interpolate_distance s hu k
  omega

/-- The analogous terminal estimate uses reverse indexing. -/
theorem terminal_clearance (s a b : Nat) (hs : 0 <s) (hb : b ≤s)
    (l : List Point) (hn : l.Nodup) (hc : l.IsChain UnitStep) (hl : 2 ≤l.length)
    (q : Point) (hq : q ∈core s a b l) :
    b≤IntegerGrid.manhattan (scale s (l[l.length-1]'(by omega))) q := by
  by_contra h
  have hd : IntegerGrid.manhattan (scale s (l[l.length-1]'(by omega))) q<s := by omega
  obtain ⟨k,hk,he⟩ := getElem_terminal_neighborhood s hs l hn hc hl q
    (mem_subdivide s a b l q hq) hd
  have hi := index_bounds a b (subdivide s l) (subdivide_nodup s l hn hc) q hq
    ((subdivide s l).length-1-k) _ he
  have he' := he.trans (subdivide_getElem_terminal s hs l hl k hk)
  have hu : UnitStep (l[l.length-1]'(by omega)) (l[l.length-2]'(by omega)) := by
    have hu := LatticeRouteDirections.neighborPoint_step l true hl hc
    simpa [LatticeRouteDirections.endpointPoint,LatticeRouteDirections.neighborPoint,
      LatticeRouteDirections.orient,List.getElem_reverse,Nat.sub_sub,
      LatticeRouteDirections.UnitStep] using hu
  have hm : IntegerGrid.manhattan (scale s (l[l.length-1]'(by omega))) q=k := by
    rw [he']
    exact interpolate_distance s hu k
  omega

theorem unrelated_clearance (s a b : Nat) (l : List Point) (hc : l.IsChain UnitStep)
    (v : Point) (hv : v ∉l) (q : Point) (hq : q ∈core s a b l) :
    s≤IntegerGrid.manhattan q (scale s v) :=
  subdivide_vertex_clearance s l hc v hv q (mem_subdivide s a b l q hq)

end GridHardness.LatticeRouteCore
