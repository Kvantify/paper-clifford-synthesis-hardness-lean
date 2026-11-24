/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteSubdivision
public import GridHardness.LatticeRouteSeparation

/-!
# Lattice Endpoint Neighborhood

A subdivided simple lattice route can approach one of its original
endpoints by less than the dilation scale only along its first or last
edge. The interpolation and list-index statements locate these points
precisely, for later replacement of endpoint neighborhoods.
-/

public section

namespace GridHardness.LatticeSubdivision
open CliffordSynthesis
set_option autoImplicit false

/-- Within one scale-width of the initial vertex, only the initial
subdivided edge can occur. -/
theorem initial_neighborhood (s : Nat) (_hs : 0 <s) (l : List Point)
    (hn : l.Nodup) (hc : l.IsChain UnitStep) (hl : 2 ≤l.length)
    (q : Point) (hq : q ∈subdivide s l)
    (hd : IntegerGrid.manhattan (scale s (l[0]'(by omega))) q <s) :
    ∃ k, k<s ∧ q=interpolate s (l[0]'(by omega)) (l[1]'(by omega)) k := by
  cases l with
  | nil => simp at hl
  | cons a l =>
    cases l with
    | nil => simp at hl
    | cons b l =>
      rw [subdivide,List.mem_append] at hq
      rcases hq with hq | hq
      · obtain ⟨k,hk,he⟩ := (mem_segmentInit s a b q).mp hq
        exact ⟨k,hk,he.symm⟩
      · have hsep := subdivide_vertex_clearance s (b::l) hc.tail a
          (List.nodup_cons.mp hn).1 q hq
        change IntegerGrid.manhattan (scale s a) q<s at hd
        rw [IntegerGrid.manhattan_comm] at hsep
        omega

/-- Within one scale-width of the final vertex, only the final
subdivided edge can occur, indexed backwards from that vertex. -/
theorem terminal_neighborhood (s : Nat) (_hs : 0 <s) (l : List Point)
    (hn : l.Nodup) (hc : l.IsChain UnitStep) (hl : 2 ≤l.length)
    (q : Point) (hq : q ∈subdivide s l)
    (hd : IntegerGrid.manhattan (scale s (l[l.length -1]'(by omega))) q <s) :
    ∃ k, k<s ∧ q=interpolate s (l[l.length-1]'(by omega))
      (l[l.length-2]'(by omega)) k := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    cases l with
    | nil => simp at hl
    | cons b l =>
      cases l with
      | nil =>
        have hseg : subdivide s [a,b]=segment s a b := by simp [subdivide]
        rw [hseg] at hq
        obtain ⟨t,ht,he⟩ := (mem_segment s a b q).mp hq
        have ht0 : 0<t := by
          by_contra hn
          have ht0 : t=0 := by omega
          subst t
          rw [interpolate_zero] at he
          subst q
          change IntegerGrid.manhattan (scale s b) (scale s a)<s at hd
          rw [scale_manhattan,IntegerGrid.manhattan_comm] at hd
          have hu := (List.isChain_cons_cons.mp hc).1
          change IntegerGrid.manhattan a b=1 at hu
          rw [hu,Nat.mul_one] at hd
          omega
        refine ⟨s-t,by omega,?_⟩
        simpa using he.symm.trans (interpolate_reverse s a b ht)
      | cons c l =>
        rw [subdivide,List.mem_append] at hq
        rcases hq with hq | hq
        · obtain ⟨t,ht,he⟩ := (mem_segmentInit s a b q).mp hq
          let z := (a::b::c::l)[(a::b::c::l).length-1]'(by simp)
          have hz : z∈c::l := by
            dsimp [z]
            exact List.getElem_mem _
          have han := (List.nodup_cons.mp hn).1
          have hbn := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
          have haz : a≠z := fun he => han (List.mem_cons_of_mem _ (he ▸ hz))
          have hbz : b≠z := fun he => hbn (he ▸ hz)
          have hsep := interpolate_vertex_separation s
            (List.isChain_cons_cons.mp hc).1 haz hbz (Nat.le_of_lt ht)
          rw [he,IntegerGrid.manhattan_comm] at hsep
          change IntegerGrid.manhattan (scale s z) q<s at hd
          omega
        · have hd' : IntegerGrid.manhattan
              (scale s ((b::c::l)[(b::c::l).length-1]'(by simp))) q<s := by
            simpa only [List.length_cons, Nat.add_sub_cancel, List.getElem_cons_succ] using hd
          obtain ⟨k,hk,hkq⟩ := ih (List.nodup_cons.mp hn).2 hc.tail (by simp) hq hd'
          refine ⟨k,hk,?_⟩
          simpa using hkq

/-- Near the initial endpoint, the subdivision index is less than the scale. -/
theorem getElem_initial_neighborhood (s : Nat) (hs : 0 <s) (l : List Point)
    (hn : l.Nodup) (hc : l.IsChain UnitStep) (hl : 2 ≤l.length)
    (q : Point) (hq : q ∈subdivide s l)
    (hd : IntegerGrid.manhattan (scale s (l[0]'(by omega))) q <s) :
    ∃ k, ∃ hk : k<s, q=(subdivide s l)[k]'(by
      rw [subdivide_length s l (by intro he; simp [he] at hl)]
      have hm := Nat.mul_le_mul_left s (show 1≤l.length-1 by omega)
      omega) := by
  obtain ⟨k,hk,he⟩ := initial_neighborhood s hs l hn hc hl q hq hd
  exact ⟨k,hk,he.trans (subdivide_getElem_initial s l hl k hk).symm⟩

/-- Near the final endpoint, the reverse subdivision index is less than the scale. -/
theorem getElem_terminal_neighborhood (s : Nat) (hs : 0 <s) (l : List Point)
    (hn : l.Nodup) (hc : l.IsChain UnitStep) (hl : 2 ≤l.length)
    (q : Point) (hq : q ∈subdivide s l)
    (hd : IntegerGrid.manhattan (scale s (l[l.length -1]'(by omega))) q <s) :
    ∃ k, ∃ _hk : k<s,
      q=(subdivide s l)[(subdivide s l).length-1-k]'(by
        have hlen := subdivide_length s l (by intro he; simp [he] at hl)
        omega) := by
  obtain ⟨k,hk,he⟩ := terminal_neighborhood s hs l hn hc hl q hq hd
  exact ⟨k,hk,he.trans (subdivide_getElem_terminal s hs l hl k hk).symm⟩

end GridHardness.LatticeSubdivision
