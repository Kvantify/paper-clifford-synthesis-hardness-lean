/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingRetirementSeparation

/-!
# SAT Crossing Retirement Horizontal

Intersections of final retirement segments with the horizontal crossing
connections. Only a shared row-zero port at an extreme crossing is possible;
all other pairs are disjoint.
-/

public section

namespace GridHardness.SatCrossingRetirement.Connections
open CliffordSynthesis PermutationWireLayout SatCrossingLattice Segments Separation
set_option autoImplicit false
variable {n : Nat} (p : Equiv.Perm (Fin n))

/-- A horizontal connector cannot meet either horizontal stretch of a
retirement route; any meeting lies in the retirement's vertical lane. -/
theorem whole_horizontal_vertical_part (last : Option (Fin n)) (a i k j : Fin n)
    (ha : LastInRow p last a) (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j)
    (r : Fin 4) (q : Point) (hq : q ∈Placement.route p last a r)
    (ht : q ∈SatCrossingHorizontal.upperRoute p i k j ∨
      q ∈SatCrossingHorizontal.lowerRoute p i k j) :
    q.1=SatCrossingRouting.lane a r ∧
      512*low a+offset r≤q.2 ∧ q.2≤512*high p a+offset r := by
  have hm := (whole_mem p last a (lastInRow_before p last a ha) r q).mp hq
  have hn := SatCrossingHorizontal.route_bounds p i k j hh.2.2.1 q ht
  have ho := offset_bounds r
  rcases hm with hm | hm | hm
  · have haj : a=j := by
      apply high_injective p
      omega
    subst a
    have hk := active_left_bound p last j k ha hh.2.1
    omega
  · exact hm
  · have hal := low_bounds a
    have hjh := high_bounds p j
    omega

/-- A common point is necessarily on lane zero of the connector's old
cell. An intervening column would itself be an omitted active crossing. -/
theorem whole_horizontal_same_column (last : Option (Fin n)) (a i k j : Fin n)
    (ha : LastInRow p last a) (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j)
    (r : Fin 4) (q : Point) (hq : q ∈Placement.route p last a r)
    (ht : q ∈SatCrossingHorizontal.upperRoute p i k j ∨
      q ∈SatCrossingHorizontal.lowerRoute p i k j) : a=i ∧ r=0 := by
  have hv := whole_horizontal_vertical_part p last a i k j ha hh r q hq ht
  have hx := SatCrossingHorizontal.route_bounds p i k j hh.2.2.1 q ht
  have hr := r.isLt
  have ho := offset_bounds r
  dsimp [SatCrossingRouting.lane] at hv
  have hia : i≤a := by
    by_contra h
    have hl := low_lt_low (show a < i from by omega)
    omega
  have hak : a<k := by
    by_contra h
    have hl : low k≤low a := by dsimp [low]; omega
    omega
  by_cases hai : a=i
  · refine ⟨hai,?_⟩
    subst a
    apply Fin.ext
    dsimp
    omega
  · have hia' : i < a := lt_of_le_of_ne hia (Ne.symm hai)
    have haj : a<j := hak.trans hh.2.1.1
    have hpa : p a≤p j := by
      by_contra h
      have hact : SatCrossingRouting.Active p a j := ⟨haj,by omega⟩
      have hle := hh.2.2.2 a hact hia'
      omega
    have hneq : p a≠p j := fun h => (ne_of_lt haj) (p.injective h)
    have hlt : p a<p j := lt_of_le_of_ne hpa hneq
    have hh' := (high_lt_high p).mpr hlt
    omega

theorem whole_upper_intersection_iff (last : Option (Fin n)) (a i k j : Fin n)
    (ha : LastInRow p last a) (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j)
    (r : Fin 4) (q : Point) :
    (q∈Placement.route p last a r ∧ q∈SatCrossingHorizontal.upperRoute p i k j) ↔
      a=i ∧ r=0 ∧ q=point p (i,j) (XorLine.row 0 false) := by
  constructor
  · rintro ⟨hq,ht⟩
    obtain ⟨hai,hr⟩ := whole_horizontal_same_column p last a i k j ha hh r q hq (Or.inl ht)
    subst a
    subst r
    have hv := whole_horizontal_vertical_part p last i i k j ha hh 0 q hq (Or.inl ht)
    have hx : q.1≤512*low i+45 := by simpa [SatCrossingRouting.lane] using le_of_eq hv.1
    have he := SatCrossingHorizontal.upperPath_left _ _ _
      (SatCrossingHorizontal.gapLength_pos i k hh.2.2.1) q ht hx
    exact ⟨rfl,rfl,he.trans (SatCrossingHorizontal.row_zero_coordinates p (i,j)).1.symm⟩
  · rintro ⟨hai,hr,hpoint⟩
    subst a
    subst r
    subst q
    refine ⟨?_,List.mem_of_head? (SatCrossingHorizontal.route_endpoints p i k j hh.2.2.1).1⟩
    have hp := Placement.future_row_ports p last i j (lastInRow_before p last i ha) hh.1 0
    exact hp.1

theorem whole_lower_intersection_iff (last : Option (Fin n)) (a i k j : Fin n)
    (ha : LastInRow p last a) (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j)
    (r : Fin 4) (q : Point) :
    (q∈Placement.route p last a r ∧ q∈SatCrossingHorizontal.lowerRoute p i k j) ↔
      a=i ∧ r=0 ∧ q=point p (i,j) (XorLine.row 0 true) := by
  constructor
  · rintro ⟨hq,ht⟩
    obtain ⟨hai,hr⟩ := whole_horizontal_same_column p last a i k j ha hh r q hq (Or.inr ht)
    subst a
    subst r
    have hv := whole_horizontal_vertical_part p last i i k j ha hh 0 q hq (Or.inr ht)
    have hx : q.1≤512*low i+45 := by simpa [SatCrossingRouting.lane] using le_of_eq hv.1
    have he := SatCrossingHorizontal.lowerPath_left _ _ _
      (SatCrossingHorizontal.gapLength_pos i k hh.2.2.1) q ht hx
    exact ⟨rfl,rfl,he.trans (SatCrossingHorizontal.row_zero_coordinates p (i,j)).2.symm⟩
  · rintro ⟨hai,hr,hpoint⟩
    subst a
    subst r
    subst q
    refine ⟨?_,List.mem_of_getLast? (SatCrossingHorizontal.route_endpoints p i k j hh.2.2.1).2.2.2⟩
    have hp := Placement.future_row_ports p last i j (lastInRow_before p last i ha) hh.1 0
    exact hp.2

theorem upper_upper_intersection_iff (last : Option (Fin n)) (a b i k j : Fin n)
    (ha : LastInRow p last a) (hb : LastInColumn p a b)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j) (r : Fin 4) (q : Point) :
    (q∈upper p last a b r ∧ q∈SatCrossingHorizontal.upperRoute p i k j) ↔
      a=i ∧ b=j ∧ r=0 ∧ q=point p (i,j) (XorLine.row 0 false) := by
  have hl := lastInRow_before p last a ha
  constructor
  · rintro ⟨hq,ht⟩
    obtain ⟨hai,hr,hpoint⟩ := (whole_upper_intersection_iff p last a i k j ha hh r q).mp
      ⟨upper_subset p last a b hl hb.1 r hq,ht⟩
    subst a
    subst r
    have hm := (upper_mem p last i b hl hb.1 0 q).mp hq
    have hq' := hpoint.trans (SatCrossingHorizontal.row_zero_coordinates p (i,j)).1
    have hj := hb.2 j hh.1
    have hij := (high_lt_high p).mpr hh.1.2
    have hj' : high p j≤high p b := by dsimp [high]; omega
    have he : b=j := by
      apply high_injective p
      rw [hq'] at hm
      dsimp [offset] at hm
      rcases hm with hm | hm <;> omega
    exact ⟨rfl,he,rfl,hpoint⟩
  · rintro ⟨hai,hbj,hr,hpoint⟩
    subst a
    subst b
    subst r
    subst q
    refine ⟨?_,List.mem_of_head? (SatCrossingHorizontal.route_endpoints p i k j hh.2.2.1).1⟩
    rw [(SatCrossingHorizontal.row_zero_coordinates p (i,j)).1,upper_mem p last i j hl hb.1]
    have hij := (high_lt_high p).mpr hb.1.2
    right
    dsimp [SatCrossingRouting.lane,offset]
    exact ⟨rfl,le_rfl,by omega⟩

theorem lower_lower_intersection_iff (last : Option (Fin n)) (a b i k j : Fin n)
    (ha : LastInRow p last a) (hb : FirstInColumn p a b)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j) (r : Fin 4) (q : Point) :
    (q∈lower p last a b r ∧ q∈SatCrossingHorizontal.lowerRoute p i k j) ↔
      a=i ∧ b=j ∧ r=0 ∧ q=point p (i,j) (XorLine.row 0 true) := by
  have hl := lastInRow_before p last a ha
  constructor
  · rintro ⟨hq,ht⟩
    obtain ⟨hai,hr,hpoint⟩ := (whole_lower_intersection_iff p last a i k j ha hh r q).mp
      ⟨lower_subset p last a b hl hb.1 r hq,ht⟩
    subst a
    subst r
    have hm := (lower_mem p last i b hl hb.1 0 q).mp hq
    have hq' := hpoint.trans (SatCrossingHorizontal.row_zero_coordinates p (i,j)).2
    have hj := hb.2 j hh.1
    have hi := low_bounds i
    have hjh := high_bounds p j
    have hj' : high p b≤high p j := by dsimp [high]; omega
    have he : b=j := by
      apply high_injective p
      rw [hq'] at hm
      dsimp [offset] at hm
      rcases hm with hm | hm <;> omega
    exact ⟨rfl,he,rfl,hpoint⟩
  · rintro ⟨hai,hbj,hr,hpoint⟩
    subst a
    subst b
    subst r
    subst q
    refine ⟨?_,List.mem_of_getLast? (SatCrossingHorizontal.route_endpoints p i k j hh.2.2.1).2.2.2⟩
    rw [(SatCrossingHorizontal.row_zero_coordinates p (i,j)).2,lower_mem p last i j hl hb.1]
    have hi := low_bounds i
    have hj := high_bounds p j
    left
    dsimp [SatCrossingRouting.lane,offset]
    exact ⟨rfl,by omega,le_rfl⟩

theorem upper_lower_disjoint (last : Option (Fin n)) (a b i k j : Fin n)
    (ha : LastInRow p last a) (hb : LastInColumn p a b)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j) (r : Fin 4) :
    (upper p last a b r).Disjoint (SatCrossingHorizontal.lowerRoute p i k j) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have hl := lastInRow_before p last a ha
  obtain ⟨hai,hr,hpoint⟩ := (whole_lower_intersection_iff p last a i k j ha hh r q).mp
    ⟨upper_subset p last a b hl hb.1 r hq,ht⟩
  subst a
  subst r
  have hm := (upper_mem p last i b hl hb.1 0 q).mp hq
  rw [hpoint,(SatCrossingHorizontal.row_zero_coordinates p (i,j)).2] at hm
  have hj := hb.2 j hh.1
  have hj' : high p j≤high p b := by dsimp [high]; omega
  have hij := (high_lt_high p).mpr hh.1.2
  dsimp [offset] at hm
  rcases hm with hm | hm <;> omega

theorem lower_upper_disjoint (last : Option (Fin n)) (a b i k j : Fin n)
    (ha : LastInRow p last a) (hb : FirstInColumn p a b)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j) (r : Fin 4) :
    (lower p last a b r).Disjoint (SatCrossingHorizontal.upperRoute p i k j) := by
  apply List.disjoint_left.mpr
  intro q hq ht
  have hl := lastInRow_before p last a ha
  obtain ⟨hai,hr,hpoint⟩ := (whole_upper_intersection_iff p last a i k j ha hh r q).mp
    ⟨lower_subset p last a b hl hb.1 r hq,ht⟩
  subst a
  subst r
  have hm := (lower_mem p last i b hl hb.1 0 q).mp hq
  rw [hpoint,(SatCrossingHorizontal.row_zero_coordinates p (i,j)).1] at hm
  have hj := hb.2 j hh.1
  have hj' : high p b≤high p j := by dsimp [high]; omega
  have hi := low_bounds i
  have hjh := high_bounds p j
  dsimp [offset] at hm
  rcases hm with hm | hm <;> omega

theorem empty_horizontal_disjoint (last : Option (Fin n)) (a i k j : Fin n)
    (ha : LastInRow p last a) (he : EmptyColumn p a)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j) (r : Fin 4) :
    (Placement.route p last a r).Disjoint (SatCrossingHorizontal.upperRoute p i k j) ∧
    (Placement.route p last a r).Disjoint (SatCrossingHorizontal.lowerRoute p i k j) := by
  constructor
  · apply List.disjoint_left.mpr
    intro q hq ht
    have ha' := ((whole_upper_intersection_iff p last a i k j ha hh r q).mp ⟨hq,ht⟩).1
    subst a
    exact he j hh.1
  · apply List.disjoint_left.mpr
    intro q hq ht
    have ha' := ((whole_lower_intersection_iff p last a i k j ha hh r q).mp ⟨hq,ht⟩).1
    subst a
    exact he j hh.1

end GridHardness.SatCrossingRetirement.Connections
