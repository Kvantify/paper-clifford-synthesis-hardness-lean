/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRetirementLinks

/-!
# SAT Crossing Retirement Separation

Simultaneous separation of the retirement lanes. The last crossing in
an actual row determines where its remaining horizontal stretch starts;
this combinatorial condition excludes intersections with other wires.
-/

public section

namespace GridHardness.SatCrossingRetirement.Separation
open CliffordSynthesis PermutationWireLayout SatCrossingLattice Segments
set_option autoImplicit false
variable {n : Nat} (p : Equiv.Perm (Fin n))

theorem active_left_bound (last : Option (Fin n)) (i a : Fin n)
    (hl : LastInRow p last i) (ha : SatCrossingRouting.Active p a i) :
    512*low a+55≤Placement.left last := by
  cases last with
  | none => exact False.elim (hl a ha)
  | some k =>
    have hk := hl.2 a ha
    dsimp [Placement.left,low]
    omega

theorem lane_left_of_retirement (last : Option (Fin n)) (i a : Fin n)
    (hl : LastInRow p last i) (ha : SatCrossingRouting.Active p a i) (r : Fin 4) :
    SatCrossingRouting.lane a r<Placement.left last := by
  have hb := active_left_bound p last i a hl ha
  dsimp [SatCrossingRouting.lane]
  omega

theorem distinct_column_lanes (i a : Fin n) (hia : i ≠a) (r s : Fin 4) :
    SatCrossingRouting.lane i r≠SatCrossingRouting.lane a s := by
  intro he
  have hr := r.isLt
  have hs := s.isLt
  have hl : low i≠low a := fun h => hia (low_injective h)
  dsimp [SatCrossingRouting.lane] at he
  omega

/-- A horizontal false-side stretch cannot meet the vertical part of a
retirement lane belonging to another wire. -/
theorem top_vertical_clear (last : Option (Fin n)) (i a : Fin n)
    (hl : LastInRow p last i) (hia : i ≠a) (r s : Fin 4) (q : Point)
    (hq : q.2 =512 *high p i +offset r ∧ Placement.left last ≤q.1 ∧ q.1 ≤SatCrossingRouting.lane i r)
    (ht : q.1 =SatCrossingRouting.lane a s ∧ q.2 ≤512 *high p a +offset s) : False := by
  have hr := r.isLt
  have hs := s.isLt
  have hor := offset_bounds r
  have hos := offset_bounds s
  have hai : a < i := by
    by_contra h
    have hle : low i<low a := low_lt_low (lt_of_le_of_ne (by omega) hia)
    dsimp [SatCrossingRouting.lane] at hq ht
    omega
  have hpi : p i<p a := by
    have hh : high p i≠high p a := fun h => hia (high_injective p h)
    apply (high_lt_high p).mp
    omega
  have hx := lane_left_of_retirement p last i a hl ⟨hai,hpi⟩ s
  omega

/-- A horizontal variable-side stretch cannot meet another wire's vertical
lane: lower wire order agrees with the order of the vertical columns. -/
theorem bottom_vertical_clear (i a : Fin n) (hia : i ≠a) (r s : Fin 4) (q : Point)
    (hq : q.2 =512 *low i +offset r ∧ SatCrossingRouting.lane i r ≤q.1)
    (ht : q.1 =SatCrossingRouting.lane a s ∧ 512 *low a +offset s ≤q.2) : False := by
  have hr := r.isLt
  have hs := s.isLt
  have hor := offset_bounds r
  have hos := offset_bounds s
  have hia' : i < a := by
    by_contra h
    have hle : low a<low i := low_lt_low (lt_of_le_of_ne (by omega) (Ne.symm hia))
    dsimp [SatCrossingRouting.lane] at hq ht
    omega
  have hh := low_lt_low hia'
  omega

/-- Complete retirement lanes of different wires are disjoint, even before
removing their portions subsequently occupied by crossing cells. -/
theorem whole_different_wires (li la : Option (Fin n)) (i a : Fin n)
    (hi : LastInRow p li i) (ha : LastInRow p la a) (hia : i ≠a) (r s : Fin 4) :
    (Placement.route p li i r).Disjoint (Placement.route p la a s) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have hm := (whole_mem p li i (lastInRow_before p li i hi) r q).mp hq
  have hn := (whole_mem p la a (lastInRow_before p la a ha) s q).mp ht
  have hor := offset_bounds r
  have hos := offset_bounds s
  have hhigh : high p i≠high p a := fun h => hia (high_injective p h)
  have hlow : low i≠low a := fun h => hia (low_injective h)
  have hil := low_bounds i
  have hal := low_bounds a
  have hih := high_bounds p i
  have hah := high_bounds p a
  rcases hm with hm | hm | hm <;> rcases hn with hn | hn | hn
  · omega
  · exact top_vertical_clear p li i a hi hia r s q hm ⟨hn.1,hn.2.2⟩
  · omega
  · exact top_vertical_clear p la a i ha (Ne.symm hia) s r q hn ⟨hm.1,hm.2.2⟩
  · exact distinct_column_lanes i a hia r s (hm.1.symm.trans hn.1)
  · exact bottom_vertical_clear a i (Ne.symm hia) s r q ⟨hn.1,hn.2.1⟩ ⟨hm.1,hm.2.1⟩
  · omega
  · exact bottom_vertical_clear i a hia r s q ⟨hm.1,hm.2.1⟩ ⟨hn.1,hn.2.1⟩
  · omega

/-- A common point of a complete retirement route and a vertical connector
forces the connector to belong to the same wire column. -/
theorem whole_vertical_same_column (last : Option (Fin n)) (i a b c : Fin n)
    (hi : LastInRow p last i) (hv : SatCrossingRouting.Consecutive p a b c)
    (r s : Fin 4) (q : Point) (hq : q ∈Placement.route p last i r)
    (ht : q ∈SatCrossingRouting.route p a b c s) : a=i := by
  by_contra hai
  have hia : i≠a := Ne.symm hai
  have hm := (whole_mem p last i (lastInRow_before p last i hi) r q).mp hq
  have hn := (SatCrossingRouting.route_mem p a b c hv.2.2.1 s q).mp ht
  have hc := (high_lt_high p).mpr hv.2.1.2
  have ha := low_bounds a
  have hb := high_bounds p b
  have hos := offset_bounds s
  rcases hm with hm | hm | hm
  · exact top_vertical_clear p last i a hi hia r s q hm ⟨hn.1,by omega⟩
  · exact distinct_column_lanes i a hia r s (hm.1.symm.trans hn.1)
  · exact bottom_vertical_clear i a hia r s q ⟨hm.1,hm.2.1⟩ ⟨hn.1,by omega⟩

/-- Upper final tails stop above the highest active cell and therefore do
not meet any vertical intercell connector. -/
theorem upper_vertical_disjoint (last : Option (Fin n)) (i j a b c : Fin n)
    (hi : LastInRow p last i) (hj : LastInColumn p i j)
    (hv : SatCrossingRouting.Consecutive p a b c) (r s : Fin 4) :
    (upper p last i j r).Disjoint (SatCrossingRouting.route p a b c s) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have hl := lastInRow_before p last i hi
  have hai := whole_vertical_same_column p last i a b c hi hv r s q
    (upper_subset p last i j hl hj.1 r hq) ht
  subst a
  have hm := (upper_mem p last i j hl hj.1 r q).mp hq
  have hn := (SatCrossingRouting.route_mem p i b c hv.2.2.1 s q).mp ht
  have hc := hj.2 c hv.2.1
  have hc' : high p c≤high p j := by dsimp [high]; omega
  have hh := (high_lt_high p).mpr hj.1.2
  have ho := offset_bounds r
  rcases hm with hm | hm <;> omega

theorem lower_vertical_disjoint (last : Option (Fin n)) (i j a b c : Fin n)
    (hi : LastInRow p last i) (hj : FirstInColumn p i j)
    (hv : SatCrossingRouting.Consecutive p a b c) (r s : Fin 4) :
    (lower p last i j r).Disjoint (SatCrossingRouting.route p a b c s) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have hl := lastInRow_before p last i hi
  have hai := whole_vertical_same_column p last i a b c hi hv r s q
    (lower_subset p last i j hl hj.1 r hq) ht
  subst a
  have hm := (lower_mem p last i j hl hj.1 r q).mp hq
  have hn := (SatCrossingRouting.route_mem p i b c hv.2.2.1 s q).mp ht
  have hb := hj.2 b hv.1
  have hb' : high p j≤high p b := by dsimp [high]; omega
  have hi' := low_bounds i
  have hj' := high_bounds p j
  have ho := offset_bounds r
  rcases hm with hm | hm <;> omega

theorem empty_vertical_disjoint (last : Option (Fin n)) (i a b c : Fin n)
    (hi : LastInRow p last i) (he : EmptyColumn p i)
    (hv : SatCrossingRouting.Consecutive p a b c) (r s : Fin 4) :
    (Placement.route p last i r).Disjoint (SatCrossingRouting.route p a b c s) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have hai := whole_vertical_same_column p last i a b c hi hv r s q hq ht
  subst a
  exact he b hv.1

end GridHardness.SatCrossingRetirement.Separation
