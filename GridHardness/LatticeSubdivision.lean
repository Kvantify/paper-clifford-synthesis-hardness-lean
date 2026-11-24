/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridGeometry
public import Mathlib.Data.List.Range

/-!
# Lattice Subdivision

Scale and subdivide axis-aligned unit steps into induced paths in the integer lattice.
-/

@[expose] public section

set_option autoImplicit false

namespace GridHardness.LatticeSubdivision
open CliffordSynthesis

abbrev Point := Int × Int
abbrev UnitStep (p q : Point) : Prop := IntegerGrid.manhattan p q = 1

/-- Uniform dilation of the integer lattice. -/
def scale (s : Nat) (p : Point) : Point := ((s : Int)*p.1, (s : Int)*p.2)

/-- Integer interpolation along a dilated unit lattice edge. -/
def interpolate (s : Nat) (p q : Point) (t : Nat) : Point :=
  ((s : Int)*p.1 + (t : Int)*(q.1-p.1),
   (s : Int)*p.2 + (t : Int)*(q.2-p.2))

/-- The inclusive subdivided edge, with `s+1` lattice points. -/
def segment (s : Nat) (p q : Point) : List Point :=
  (List.range (s+1)).map (interpolate s p q)

/-- The half-open subdivided edge, used when adjoining successive edges. -/
def segmentInit (s : Nat) (p q : Point) : List Point :=
  (List.range s).map (interpolate s p q)

@[simp] theorem interpolate_zero (s : Nat) (p q : Point) :
    interpolate s p q 0 = scale s p := by simp [interpolate, scale]

@[simp] theorem interpolate_scale (s : Nat) (p q : Point) :
    interpolate s p q s = scale s q := by
  apply Prod.ext <;> dsimp [interpolate,scale] <;> ring

@[simp] theorem segment_length (s : Nat) (p q : Point) :
    (segment s p q).length = s+1 := by simp [segment]

@[simp] theorem segmentInit_length (s : Nat) (p q : Point) :
    (segmentInit s p q).length = s := by simp [segmentInit]

@[simp] theorem segment_eq_init_append (s : Nat) (p q : Point) :
    segment s p q = segmentInit s p q ++ [scale s q] := by
  simp [segment,segmentInit,List.range_succ]

@[simp] theorem mem_segment (s : Nat) (p q z : Point) :
    z ∈ segment s p q ↔ ∃ t, t ≤ s ∧ interpolate s p q t = z := by
  simp only [segment, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ht, hz⟩; exact ⟨t, by omega, hz⟩
  · rintro ⟨t, ht, hz⟩; exact ⟨t, by omega, hz⟩

@[simp] theorem mem_segmentInit (s : Nat) (p q z : Point) :
    z ∈ segmentInit s p q ↔ ∃ t, t < s ∧ interpolate s p q t = z := by
  simp [segmentInit]

@[simp] theorem segment_head (s : Nat) (p q : Point) :
    (segment s p q).head? = some (scale s p) := by
  simp [segment,List.range_succ_eq_map]

@[simp] theorem segment_getLast (s : Nat) (p q : Point) :
    (segment s p q).getLast? = some (scale s q) := by
  rw [segment_eq_init_append]
  simp

@[simp] theorem segmentInit_head {s : Nat} (hs : 0 < s) (p q : Point) :
    (segmentInit s p q).head? = some (scale s p) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  simp [segmentInit,List.range_succ_eq_map]

theorem interpolate_injective (s : Nat) {p q : Point} (h : UnitStep p q) :
    Function.Injective (interpolate s p q) := by
  intro t r ht
  rcases (manhattan_one_iff p q).mp h with rfl | rfl | rfl | rfl <;>
    simp [interpolate] at ht <;> omega

theorem interpolate_step (s : Nat) {p q : Point} (h : UnitStep p q) (t : Nat) :
    UnitStep (interpolate s p q t) (interpolate s p q (t+1)) := by
  rcases (manhattan_one_iff p q).mp h with rfl | rfl | rfl | rfl <;>
    simp [interpolate, UnitStep, IntegerGrid.manhattan]

theorem segment_nodup (s : Nat) {p q : Point} (h : UnitStep p q) :
    (segment s p q).Nodup :=
  List.nodup_range.map (interpolate_injective s h)

theorem segmentInit_nodup (s : Nat) {p q : Point} (h : UnitStep p q) :
    (segmentInit s p q).Nodup :=
  List.nodup_range.map (interpolate_injective s h)

theorem segment_chain (s : Nat) {p q : Point} (h : UnitStep p q) :
    (segment s p q).IsChain UnitStep := by
  rw [segment,List.isChain_map,List.isChain_range_succ]
  intro t ht
  exact interpolate_step s h t

theorem segmentInit_chain (s : Nat) {p q : Point} (h : UnitStep p q) :
    (segmentInit s p q).IsChain UnitStep := by
  rw [segmentInit,List.isChain_map,List.isChain_range]
  intro t ht
  exact interpolate_step s h t

/-- Uniform dilation multiplies every Manhattan distance by the scale. -/
theorem scale_manhattan (s : Nat) (p q : Point) :
    IntegerGrid.manhattan (scale s p) (scale s q) = s * IntegerGrid.manhattan p q := by
  simp only [IntegerGrid.manhattan, scale]
  rw [← mul_sub, ← mul_sub]
  simp [Int.natAbs_mul, Nat.mul_add]

/-- Every interpolation coordinate stays between its dilated endpoints. -/
theorem interpolate_bounds (s : Nat) (p q : Point) {t : Nat} (ht : t ≤ s) :
    (s : Int) * min p.1 q.1 ≤ (interpolate s p q t).1 ∧
    (interpolate s p q t).1 ≤ (s : Int) * max p.1 q.1 ∧
    (s : Int) * min p.2 q.2 ≤ (interpolate s p q t).2 ∧
    (interpolate s p q t).2 ≤ (s : Int) * max p.2 q.2 := by
  have hbound (a b : Int) :
      (s : Int) * min a b ≤ (s : Int)*a + (t : Int)*(b-a) ∧
      (s : Int)*a + (t : Int)*(b-a) ≤ (s : Int) * max a b := by
    have ht' : (t : Int) ≤ s := by exact_mod_cast ht
    have ht0 : (0 : Int) ≤ t := by omega
    have hs0 : (0 : Int) ≤ s := by omega
    by_cases hab : a ≤ b
    · rw [min_eq_left hab, max_eq_right hab]
      constructor <;> nlinarith
    · rw [min_eq_right (by omega), max_eq_left (by omega)]
      constructor <;> nlinarith
  exact ⟨(hbound p.1 q.1).1, (hbound p.1 q.1).2,
    (hbound p.2 q.2).1, (hbound p.2 q.2).2⟩

/-- Disjoint unit lattice edges have a unit gap between their coordinate boxes. -/
theorem unit_edge_box_gap {p q u v : Point} (hpq : UnitStep p q) (huv : UnitStep u v)
    (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v) :
    max p.1 q.1 + 1 ≤ min u.1 v.1 ∨ max u.1 v.1 + 1 ≤ min p.1 q.1 ∨
    max p.2 q.2 + 1 ≤ min u.2 v.2 ∨ max u.2 v.2 + 1 ≤ min p.2 q.2 := by
  rcases p with ⟨px,py⟩
  rcases u with ⟨ux,uy⟩
  rcases (manhattan_one_iff _ _).mp hpq with rfl | rfl | rfl | rfl <;>
    rcases (manhattan_one_iff _ _).mp huv with rfl | rfl | rfl | rfl <;>
    simp only [ne_eq, Prod.mk.injEq] at hpu hpv hqu hqv <;>
    dsimp <;> omega

/-- An unrelated lattice vertex has a unit gap from a unit edge's box. -/
theorem unit_edge_vertex_box_gap {p q z : Point} (hpq : UnitStep p q)
    (hpz : p ≠ z) (hqz : q ≠ z) :
    max p.1 q.1 + 1 ≤ z.1 ∨ z.1 + 1 ≤ min p.1 q.1 ∨
    max p.2 q.2 + 1 ≤ z.2 ∨ z.2 + 1 ≤ min p.2 q.2 := by
  rcases p with ⟨px,py⟩
  rcases z with ⟨zx,zy⟩
  rcases (manhattan_one_iff _ _).mp hpq with rfl | rfl | rfl | rfl <;>
    simp only [ne_eq, Prod.mk.injEq] at hpz hqz <;>
    dsimp <;> omega

/-- Subdivision separates disjoint original unit edges by at least the scale. -/
theorem interpolate_separation (s : Nat) {p q u v : Point}
    (hpq : UnitStep p q) (huv : UnitStep u v)
    (hpu : p ≠ u) (hpv : p ≠ v) (hqu : q ≠ u) (hqv : q ≠ v)
    {t r : Nat} (ht : t ≤ s) (hr : r ≤ s) :
    s ≤ IntegerGrid.manhattan (interpolate s p q t) (interpolate s u v r) := by
  obtain ⟨hpx,hqx,hpy,hqy⟩ := interpolate_bounds s p q ht
  obtain ⟨hux,hvx,huy,hvy⟩ := interpolate_bounds s u v hr
  have hs0 : (0 : Int) ≤ s := by omega
  rcases unit_edge_box_gap hpq huv hpu hpv hqu hqv with h | h | h | h
  · have hg := mul_le_mul_of_nonneg_left h hs0
    have hd : (s : Int) ≤ (interpolate s u v r).1 - (interpolate s p q t).1 := by
      nlinarith
    dsimp [IntegerGrid.manhattan]
    omega
  · have hg := mul_le_mul_of_nonneg_left h hs0
    have hd : (s : Int) ≤ (interpolate s p q t).1 - (interpolate s u v r).1 := by
      nlinarith
    dsimp [IntegerGrid.manhattan]
    omega
  · have hg := mul_le_mul_of_nonneg_left h hs0
    have hd : (s : Int) ≤ (interpolate s u v r).2 - (interpolate s p q t).2 := by
      nlinarith
    dsimp [IntegerGrid.manhattan]
    omega
  · have hg := mul_le_mul_of_nonneg_left h hs0
    have hd : (s : Int) ≤ (interpolate s p q t).2 - (interpolate s u v r).2 := by
      nlinarith
    dsimp [IntegerGrid.manhattan]
    omega

/-- A dilated vertex stays far from every edge to which it does not belong. -/
theorem interpolate_vertex_separation (s : Nat) {p q z : Point}
    (hpq : UnitStep p q) (hpz : p ≠ z) (hqz : q ≠ z)
    {t : Nat} (ht : t ≤ s) :
    s ≤ IntegerGrid.manhattan (interpolate s p q t) (scale s z) := by
  obtain ⟨hpx,hqx,hpy,hqy⟩ := interpolate_bounds s p q ht
  have hs0 : (0 : Int) ≤ s := by omega
  rcases unit_edge_vertex_box_gap hpq hpz hqz with h | h | h | h
  · have hg := mul_le_mul_of_nonneg_left h hs0
    have hd : (s : Int) ≤ (scale s z).1 - (interpolate s p q t).1 := by
      dsimp [scale]; nlinarith
    dsimp [IntegerGrid.manhattan]; omega
  · have hg := mul_le_mul_of_nonneg_left h hs0
    have hd : (s : Int) ≤ (interpolate s p q t).1 - (scale s z).1 := by
      dsimp [scale]; nlinarith
    dsimp [IntegerGrid.manhattan]; omega
  · have hg := mul_le_mul_of_nonneg_left h hs0
    have hd : (s : Int) ≤ (scale s z).2 - (interpolate s p q t).2 := by
      dsimp [scale]; nlinarith
    dsimp [IntegerGrid.manhattan]; omega
  · have hg := mul_le_mul_of_nonneg_left h hs0
    have hd : (s : Int) ≤ (interpolate s p q t).2 - (scale s z).2 := by
      dsimp [scale]; nlinarith
    dsimp [IntegerGrid.manhattan]; omega

/-- Reversing an edge reverses its interpolation parameter. -/
theorem interpolate_reverse (s : Nat) (p q : Point) {t : Nat} (ht : t ≤ s) :
    interpolate s p q t = interpolate s q p (s-t) := by
  have ht' : ((s-t : Nat) : Int) = (s : Int) - t := by omega
  apply Prod.ext <;> dsimp [interpolate] <;> rw [ht'] <;> ring

/-- A half-open edge cannot meet the next edge of a nonbacktracking lattice walk. -/
theorem interpolate_adjacent_ne (s : Nat) {p q v : Point}
    (hpq : UnitStep p q) (hqv : UnitStep q v) (hpv : p ≠ v)
    {t r : Nat} (ht : t < s) :
    interpolate s p q t ≠ interpolate s q v r := by
  intro he
  rcases p with ⟨px,py⟩
  rcases (manhattan_one_iff _ _).mp hpq with rfl | rfl | rfl | rfl <;>
    rcases (manhattan_one_iff _ _).mp hqv with rfl | rfl | rfl | rfl <;>
    simp only [ne_eq, Prod.mk.injEq] at hpv <;>
    simp [interpolate, mul_add, mul_sub] at hpv he <;> omega

/-- Coincidence with a scaled lattice vertex identifies the source of a
half-open edge. The terminal point is excluded by the strict parameter bound. -/
theorem interpolate_eq_scale_source (s : Nat) {p q z : Point}
    (hpq : UnitStep p q) {t : Nat} (ht : t < s)
    (he : interpolate s p q t = scale s z) : p = z := by
  by_contra hpz
  by_cases hqz : q = z
  · subst z
    have hi := interpolate_injective s hpq
      (he.trans (interpolate_scale s p q).symm)
    omega
  · have hsep := interpolate_vertex_separation s hpq hpz hqz (Nat.le_of_lt ht)
    rw [he] at hsep
    simp [IntegerGrid.manhattan] at hsep
    omega

/-- When two subdivided edges meet before the first edge's terminal point,
its source must be an endpoint of the other edge. -/
theorem interpolate_eq_source_endpoint (s : Nat) {p q u v : Point}
    (hpq : UnitStep p q) (huv : UnitStep u v)
    {t r : Nat} (ht : t < s) (hr : r ≤ s)
    (he : interpolate s p q t = interpolate s u v r) : p = u ∨ p = v := by
  by_contra hn
  push Not at hn
  obtain ⟨hpu,hpv⟩ := hn
  by_cases hqu : q = u
  · subst u
    exact interpolate_adjacent_ne s hpq huv hpv ht he
  by_cases hqv : q = v
  · subst v
    have hqu : UnitStep q u := by
      rcases (manhattan_one_iff _ _).mp huv with h | h | h | h <;>
        rw [h] <;> simp [UnitStep,IntegerGrid.manhattan]
    rw [interpolate_reverse s u q hr] at he
    exact interpolate_adjacent_ne s hpq hqu hpu ht he
  have hsep := interpolate_separation s hpq huv hpu hpv hqu hqv
    (Nat.le_of_lt ht) hr
  rw [he] at hsep
  simp [IntegerGrid.manhattan] at hsep
  omega

/-- Two different unit edges issuing from one vertex intersect after dilation
only at that vertex. -/
theorem interpolate_common_source (s : Nat) {p q v : Point}
    (hpq : UnitStep p q) (hpv : UnitStep p v) (hqv : q ≠ v)
    {t r : Nat} (ht : t ≤ s)
    (he : interpolate s p q t = interpolate s p v r) : t = 0 ∧ r = 0 := by
  have ht0 : t = 0 := by
    by_contra hn
    have hqp : UnitStep q p := by
      change IntegerGrid.manhattan q p = 1
      rwa [IntegerGrid.manhattan_comm]
    rw [interpolate_reverse s p q ht] at he
    exact interpolate_adjacent_ne s hqp hpv hqv (by omega) he
  subst t
  constructor
  · rfl
  · apply interpolate_injective s hpv
    simpa only [interpolate_zero] using he.symm

/-- Inclusive interpolation can hit a dilated lattice point only at one of
its original endpoints. -/
theorem interpolate_eq_scale_endpoint (s : Nat) (hs : 0 < s) {p q z : Point}
    (hpq : UnitStep p q) {t : Nat} (ht : t ≤ s)
    (he : interpolate s p q t = scale s z) : p = z ∨ q = z := by
  by_cases hpt : t < s
  · exact Or.inl (interpolate_eq_scale_source s hpq hpt he)
  by_contra hn
  push Not at hn
  have hsep := interpolate_vertex_separation s hpq hn.1 hn.2 ht
  rw [he] at hsep
  simp [IntegerGrid.manhattan] at hsep
  omega

/-- Unless two edges have the same unordered pair of endpoints, their
subdivisions can intersect only at a scaled common endpoint. -/
theorem interpolate_intersection (s : Nat) (hs : 0 < s) {p q u v : Point}
    (hpq : UnitStep p q) (huv : UnitStep u v)
    (hdirect : ¬ (p = u ∧ q = v)) (hreverse : ¬ (p = v ∧ q = u))
    {t r : Nat} (ht : t ≤ s) (hr : r ≤ s)
    (he : interpolate s p q t = interpolate s u v r) :
    ∃ z, (z = p ∨ z = q) ∧ (z = u ∨ z = v) ∧
      interpolate s p q t = scale s z := by
  by_cases hts : t = s
  · subst t
    rw [interpolate_scale] at he ⊢
    have hz := interpolate_eq_scale_endpoint s hs huv hr he.symm
    exact ⟨q, Or.inr rfl, hz.imp Eq.symm Eq.symm, rfl⟩
  have hep := interpolate_eq_source_endpoint s hpq huv (by omega) hr he
  rcases hep with hpu | hpv
  · subst u
    have hqv : q ≠ v := fun h => hdirect ⟨rfl,h⟩
    have ht0 := (interpolate_common_source s hpq huv hqv ht he).1
    exact ⟨p,Or.inl rfl,Or.inl rfl,by simp [ht0]⟩
  · subst v
    have hqu : q ≠ u := fun h => hreverse ⟨rfl,h⟩
    have hpu : UnitStep p u := by
      change IntegerGrid.manhattan p u = 1
      rwa [IntegerGrid.manhattan_comm]
    rw [interpolate_reverse s u p hr] at he
    have ht0 := (interpolate_common_source s hpq hpu hqu ht he).1
    exact ⟨p,Or.inl rfl,Or.inr rfl,by simp [ht0]⟩

end GridHardness.LatticeSubdivision
