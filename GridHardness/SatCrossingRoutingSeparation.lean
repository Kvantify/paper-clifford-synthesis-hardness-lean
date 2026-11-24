/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingHorizontalRouting

/-!
# SAT Crossing Routing Separation

Exact intersections between the horizontal and vertical connections.
The only intersections are the intended old row-zero ports; there is no
intersection at the new cell's false ports. These are geometric statements
about the concrete connection families, not a complete global SAT drawing.
-/

public section

namespace GridHardness.SatCrossingRoutingSeparation
open CliffordSynthesis PermutationWireLayout SatCrossingLattice
set_option autoImplicit false

abbrev Point := Int × Int

variable {n : Nat} (p : Equiv.Perm (Fin n))

/-- A common point must lie on lane zero of the old horizontal cell's column.
An intervening column is excluded by the actual inversion catalogue. -/
private theorem common_column (i k j a b c : Fin n) (r : Fin 4)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j)
    (hv : SatCrossingRouting.Consecutive p a b c) (q : Point)
    (hqh : q ∈ SatCrossingHorizontal.upperRoute p i k j ∨
      q ∈ SatCrossingHorizontal.lowerRoute p i k j)
    (hqv : q ∈ SatCrossingRouting.route p a b c r) : a=i ∧ r=0 := by
  have hx := SatCrossingHorizontal.route_bounds p i k j hh.2.2.1 q hqh
  have hy := (SatCrossingRouting.route_mem p a b c hv.2.2.1 r q).mp hqv
  have hr := r.isLt
  dsimp [SatCrossingRouting.lane] at hy
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
  · have hia' : i<a := lt_of_le_of_ne hia (Ne.symm hai)
    have hj : a<j := hak.trans hh.2.1.1
    have hpa : p a≤p j := by
      by_contra h
      have hact : SatCrossingRouting.Active p a j := ⟨hj,by omega⟩
      have hle := hh.2.2.2 a hact hia'
      omega
    have hpc : p c<p j := hv.2.1.2.trans_le hpa
    have hhc := (high_lt_high p).mpr hpc
    omega

/-- The upper connection meets a vertical connection precisely when the old
cell is its lower endpoint, on row-zero's positive boundary. -/
theorem upper_intersection_iff (i k j a b c : Fin n) (r : Fin 4)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j)
    (hv : SatCrossingRouting.Consecutive p a b c) (q : Point) :
    (q ∈ SatCrossingHorizontal.upperRoute p i k j ∧
      q ∈ SatCrossingRouting.route p a b c r) ↔
      a=i ∧ r=0 ∧ b=j ∧ q=point p (i,j) (XorLine.row 0 false) := by
  constructor
  · rintro ⟨hqh,hqv⟩
    obtain ⟨hai,hr⟩ := common_column p i k j a b c r hh hv q (Or.inl hqh) hqv
    subst a
    subst r
    have hy := (SatCrossingRouting.route_mem p i b c hv.2.2.1 0 q).mp hqv
    have hxp : q.1≤512*low i+45 := by simpa [SatCrossingRouting.lane] using le_of_eq hy.1
    have he := SatCrossingHorizontal.upperPath_left _ _ _
      (SatCrossingHorizontal.gapLength_pos i k hh.2.2.1) q hqh hxp
    have hport := (SatCrossingHorizontal.row_zero_coordinates p (i,j)).1
    have hq : q=point p (i,j) (XorLine.row 0 false) := he.trans hport.symm
    have hb : b=j := by
      by_contra hbj
      have hbh : high p b≠high p j := fun h => hbj (high_injective p h)
      have hpb : p b<p j := (high_lt_high p).mp (by rw [he] at hy; dsimp at hy; omega)
      have hc := hv.2.2.2 j hh.1 hpb
      have hhc : high p c≤high p j := by dsimp [high]; omega
      rw [he] at hy
      dsimp at hy
      omega
    exact ⟨rfl,rfl,hb,hq⟩
  · rintro ⟨hai,hr,hbj,hq⟩
    subst a
    subst r
    subst b
    subst q
    refine ⟨List.mem_of_head? (SatCrossingHorizontal.route_endpoints p i k j hh.2.2.1).1,?_⟩
    rw [SatCrossingRouting.route_mem p i j c hv.2.2.1,
      (SatCrossingHorizontal.row_zero_coordinates p (i,j)).1]
    have hc := (high_lt_high p).mpr hv.2.2.1
    dsimp [SatCrossingRouting.lane]
    exact ⟨by omega,le_rfl,by omega⟩

/-- The lower connection meets a vertical connection precisely when the old
cell is its upper endpoint, on row-zero's negative boundary. -/
theorem lower_intersection_iff (i k j a b c : Fin n) (r : Fin 4)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j)
    (hv : SatCrossingRouting.Consecutive p a b c) (q : Point) :
    (q ∈ SatCrossingHorizontal.lowerRoute p i k j ∧
      q ∈ SatCrossingRouting.route p a b c r) ↔
      a=i ∧ r=0 ∧ c=j ∧ q=point p (i,j) (XorLine.row 0 true) := by
  constructor
  · rintro ⟨hqh,hqv⟩
    obtain ⟨hai,hr⟩ := common_column p i k j a b c r hh hv q (Or.inr hqh) hqv
    subst a
    subst r
    have hy := (SatCrossingRouting.route_mem p i b c hv.2.2.1 0 q).mp hqv
    have hxp : q.1≤512*low i+45 := by simpa [SatCrossingRouting.lane] using le_of_eq hy.1
    have he := SatCrossingHorizontal.lowerPath_left _ _ _
      (SatCrossingHorizontal.gapLength_pos i k hh.2.2.1) q hqh hxp
    have hport := (SatCrossingHorizontal.row_zero_coordinates p (i,j)).2
    have hq : q=point p (i,j) (XorLine.row 0 true) := he.trans hport.symm
    have hc : c=j := by
      have hpb : p b<p j := (high_lt_high p).mp (by rw [he] at hy; dsimp at hy; omega)
      have hc := hv.2.2.2 j hh.1 hpb
      apply p.injective
      apply le_antisymm hc
      have hhc : high p j≤high p c := by rw [he] at hy; dsimp at hy; omega
      dsimp [high] at hhc
      omega
    exact ⟨rfl,rfl,hc,hq⟩
  · rintro ⟨hai,hr,hcj,hq⟩
    subst a
    subst r
    subst c
    subst q
    refine ⟨List.mem_of_getLast? (SatCrossingHorizontal.route_endpoints p i k j hh.2.2.1).2.2.2,?_⟩
    rw [SatCrossingRouting.route_mem p i b j hv.2.2.1,
      (SatCrossingHorizontal.row_zero_coordinates p (i,j)).2]
    have hb := (high_lt_high p).mpr hv.2.2.1
    dsimp [SatCrossingRouting.lane]
    exact ⟨by omega,by omega,le_rfl⟩

/-- Apart from a shared designated old port, upper and vertical routes are
completely vertex-disjoint. -/
theorem upper_disjoint_iff (i k j a b c : Fin n) (r : Fin 4)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j)
    (hv : SatCrossingRouting.Consecutive p a b c) :
    (SatCrossingHorizontal.upperRoute p i k j).Disjoint
      (SatCrossingRouting.route p a b c r) ↔ ¬(a=i ∧ r=0 ∧ b=j) := by
  constructor
  · intro hd he
    have hm := (upper_intersection_iff p i k j a b c r hh hv
      (point p (i,j) (XorLine.row 0 false))).mpr ⟨he.1,he.2.1,he.2.2,rfl⟩
    exact List.disjoint_left.mp hd hm.1 hm.2
  · intro he
    apply List.disjoint_left.mpr
    intro q hqh hqv
    have h := (upper_intersection_iff p i k j a b c r hh hv q).mp ⟨hqh,hqv⟩
    exact he ⟨h.1,h.2.1,h.2.2.1⟩

theorem lower_disjoint_iff (i k j a b c : Fin n) (r : Fin 4)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j)
    (hv : SatCrossingRouting.Consecutive p a b c) :
    (SatCrossingHorizontal.lowerRoute p i k j).Disjoint
      (SatCrossingRouting.route p a b c r) ↔ ¬(a=i ∧ r=0 ∧ c=j) := by
  constructor
  · intro hd he
    have hm := (lower_intersection_iff p i k j a b c r hh hv
      (point p (i,j) (XorLine.row 0 true))).mpr ⟨he.1,he.2.1,he.2.2,rfl⟩
    exact List.disjoint_left.mp hd hm.1 hm.2
  · intro he
    apply List.disjoint_left.mpr
    intro q hqh hqv
    have h := (lower_intersection_iff p i k j a b c r hh hv q).mp ⟨hqh,hqv⟩
    exact he ⟨h.1,h.2.1,h.2.2.1⟩

/-- Neither false port of the next cell lies on any vertical connecting
route. The shared vertices, when present, belong to the old cell only. -/
theorem new_false_ports_clear (i k j a b c : Fin n) (r : Fin 4)
    (hh : SatCrossingHorizontal.ConsecutiveColumns p i k j)
    (hv : SatCrossingRouting.Consecutive p a b c) :
    point p (k,j) (XorLine.inputPort 4 (.inl false)) ∉ SatCrossingRouting.route p a b c r ∧
    point p (k,j) (XorLine.outputPort 4 (.inl false)) ∉ SatCrossingRouting.route p a b c r := by
  have he := SatCrossingHorizontal.route_endpoints p i k j hh.2.2.1
  constructor
  · intro hv'
    have hm := (upper_intersection_iff p i k j a b c r hh hv _).mp
      ⟨List.mem_of_getLast? he.2.1,hv'⟩
    have hp := @point_injective n p ((k,j),XorLine.inputPort 4 (.inl false))
      ((i,j),XorLine.row 0 false) hm.2.2.2
    have hk : k=i := congrArg (fun z => z.1.1) hp
    exact (ne_of_lt hh.2.2.1) hk.symm
  · intro hv'
    have hm := (lower_intersection_iff p i k j a b c r hh hv _).mp
      ⟨List.mem_of_head? he.2.2.1,hv'⟩
    have hp := @point_injective n p ((k,j),XorLine.outputPort 4 (.inl false))
      ((i,j),XorLine.row 0 true) hm.2.2.2
    have hk : k=i := congrArg (fun z => z.1.1) hp
    exact (ne_of_lt hh.2.2.1) hk.symm

end GridHardness.SatCrossingRoutingSeparation
