/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteCore
public import GridHardness.LatticeRouteSeparation

/-!
# Lattice Route Core Separation

Quantitative separation of subdivided routes after removing their
common endpoint neighborhoods. Distinct unit edges through one lattice
vertex separate at the sum of their distances from that vertex; disjoint
unit edges retain the full dilation margin.
-/

public section

namespace GridHardness.LatticeRouteCore
open CliffordSynthesis LatticeSubdivision
set_option autoImplicit false

/-- Different unit rays at one lattice vertex separate at the sum of
longitudinal parameters. -/
theorem common_source_distance (s : Nat) {p q v : Point}
    (hpq : UnitStep p q) (hpv : UnitStep p v) (hqv : q ≠v) (t r : Nat) :
    IntegerGrid.manhattan (interpolate s p q t) (interpolate s p v r)=t+r := by
  rcases p with ⟨px,py⟩
  rcases (manhattan_one_iff _ _).mp hpq with rfl | rfl | rfl | rfl <;>
    rcases (manhattan_one_iff _ _).mp hpv with rfl | rfl | rfl | rfl <;>
    simp [interpolate,IntegerGrid.manhattan] at hqv ⊢ <;> omega

/-- The same identity expressed intrinsically as distances from the
common scaled vertex, independent of interpolation orientation. -/
theorem common_source_distance_add (s : Nat) {p q v : Point}
    (hpq : UnitStep p q) (hpv : UnitStep p v) (hqv : q ≠v) (t r : Nat) :
    IntegerGrid.manhattan (interpolate s p q t) (interpolate s p v r)=
      IntegerGrid.manhattan (scale s p) (interpolate s p q t)+
      IntegerGrid.manhattan (scale s p) (interpolate s p v r) := by
  rw [common_source_distance s hpq hpv hqv,interpolate_distance s hpq,
    interpolate_distance s hpv]

/-- Two routes with at most one common original point have a gap of at
least twice the excluded endpoint radius. The radius may be at most half
the dilation scale. This includes original routes of only two points. -/
theorem subdivision_separation (s k : Nat) (hk : 0 <k) (hks : 2 *k≤s)
    (l m : List Point) (hl : l.IsChain UnitStep) (hm : m.IsChain UnitStep)
    (hcommon : ∀ u v, u ∈l → u ∈m → v ∈l → v ∈m → u =v)
    (p q : Point) (hp : p ∈subdivide s l) (hq : q ∈subdivide s m)
    (hpl : ∀ z, z ∈l → z ∈m → k ≤IntegerGrid.manhattan (scale s z) p)
    (hqm : ∀ z, z ∈l → z ∈m → k ≤IntegerGrid.manhattan (scale s z) q) :
    2*k≤IntegerGrid.manhattan p q := by
  rcases (subdivide_mem s l p).mp hp with ⟨a,ha,rfl⟩ | ⟨a,b,hab,t,ht,rfl⟩
  · have hal : a∈l := List.mem_of_getLast? ha
    by_cases ham : a∈m
    · have hh := hpl a hal ham
      simp [IntegerGrid.manhattan] at hh
      omega
    · have hh := subdivide_vertex_clearance s m hm a ham q hq
      rw [IntegerGrid.manhattan_comm] at hh
      omega
  rcases (subdivide_mem s m q).mp hq with ⟨c,hc,rfl⟩ | ⟨c,d,hcd,r,hr,rfl⟩
  · have hcm : c∈m := List.mem_of_getLast? hc
    by_cases hcl : c∈l
    · have hh := hqm c hcl hcm
      simp [IntegerGrid.manhattan] at hh
      omega
    · have hh := subdivide_vertex_clearance s l hl c hcl _ hp
      omega
  obtain ⟨hal,hbl⟩ := edges_mem_vertices l a b hab
  obtain ⟨hcm,hdm⟩ := edges_mem_vertices m c d hcd
  have hu := edges_unit l hl a b hab
  have hv := edges_unit m hm c d hcd
  have habne : a≠b := by
    intro he
    rw [he] at hu
    simp [UnitStep,IntegerGrid.manhattan] at hu
  by_cases hac : a=c
  · subst c
    have hbd : b≠d := fun he => habne (hcommon a b hal hcm hbl (he.symm ▸ hdm))
    have he := common_source_distance_add s hu hv hbd t r
    have hp0 := hpl a hal hcm
    have hq0 := hqm a hal hcm
    omega
  by_cases had : a=d
  · subst d
    have hbc : b≠c := fun he => habne (hcommon a b hal hdm hbl (he.symm ▸ hcm))
    have hv' : UnitStep a c := by simpa only [UnitStep,IntegerGrid.manhattan_comm] using hv
    have he := common_source_distance_add s hu hv' hbc t (s-r)
    rw [← interpolate_reverse s c a (Nat.le_of_lt hr)] at he
    have hp0 := hpl a hal hdm
    have hq0 := hqm a hal hdm
    omega
  by_cases hbc : b=c
  · subst c
    have had : a≠d := fun he => habne (hcommon a b hal (he.symm ▸ hdm) hbl hcm)
    have hu' : UnitStep b a := by simpa only [UnitStep,IntegerGrid.manhattan_comm] using hu
    have he := common_source_distance_add s hu' hv had (s-t) r
    rw [← interpolate_reverse s a b (Nat.le_of_lt ht)] at he
    have hp0 := hpl b hbl hcm
    have hq0 := hqm b hbl hcm
    omega
  by_cases hbd : b=d
  · subst d
    have hac : a≠c := fun he => habne (hcommon a b hal (he.symm ▸ hcm) hbl hdm)
    have hu' : UnitStep b a := by simpa only [UnitStep,IntegerGrid.manhattan_comm] using hu
    have hv' : UnitStep b c := by simpa only [UnitStep,IntegerGrid.manhattan_comm] using hv
    have he := common_source_distance_add s hu' hv' hac (s-t) (s-r)
    rw [← interpolate_reverse s a b (Nat.le_of_lt ht),
      ← interpolate_reverse s c b (Nat.le_of_lt hr)] at he
    have hp0 := hpl b hbl hdm
    have hq0 := hqm b hbl hdm
    omega
  · exact hks.trans (interpolate_separation s hu hv hac had hbc hbd
      (Nat.le_of_lt ht) (Nat.le_of_lt hr))

end GridHardness.LatticeRouteCore
