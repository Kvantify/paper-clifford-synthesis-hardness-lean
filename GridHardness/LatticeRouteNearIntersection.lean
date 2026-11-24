/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteCoreSeparation

/-!
# Lattice Route Near Intersection

Close points on different subdivided routes must be near their shared
original vertex. The exact additive distance identity distinguishes this
local incidence case from the full dilation margin between disjoint edges.
-/

public section

namespace GridHardness.LatticeRouteCore
open CliffordSynthesis LatticeSubdivision
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Two subdivided routes with at most one common original vertex either
retain the full scale separation, or their distance is exactly the sum of
their distances from that shared scaled vertex. No endpoint cuts are assumed. -/
theorem subdivision_distance_dichotomy (s : Nat) (l m : List Point)
    (hl : l.IsChain UnitStep) (hm : m.IsChain UnitStep)
    (hcommon : ∀ u v, u ∈l → u ∈m → v ∈l → v ∈m → u =v)
    (p q : Point) (hp : p ∈subdivide s l) (hq : q ∈subdivide s m) :
    s≤IntegerGrid.manhattan p q ∨
      ∃ z, z∈l ∧ z∈m ∧ IntegerGrid.manhattan p q=
        IntegerGrid.manhattan (scale s z) p+IntegerGrid.manhattan (scale s z) q := by
  rcases (subdivide_mem s l p).mp hp with ⟨a,ha,rfl⟩ | ⟨a,b,hab,t,ht,rfl⟩
  · have hal : a∈l := List.mem_of_getLast? ha
    by_cases ham : a∈m
    · exact Or.inr ⟨a,hal,ham,by simp [IntegerGrid.manhattan]⟩
    · apply Or.inl
      rw [IntegerGrid.manhattan_comm]
      exact subdivide_vertex_clearance s m hm a ham q hq
  rcases (subdivide_mem s m q).mp hq with ⟨c,hc,rfl⟩ | ⟨c,d,hcd,r,hr,rfl⟩
  · have hcm : c∈m := List.mem_of_getLast? hc
    by_cases hcl : c∈l
    · apply Or.inr
      refine ⟨c,hcl,hcm,?_⟩
      simp only [IntegerGrid.manhattan_comm _ (scale s c)]
      simp [IntegerGrid.manhattan]
    · exact Or.inl (subdivide_vertex_clearance s l hl c hcl _ hp)
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
    exact Or.inr ⟨a,hal,hcm,common_source_distance_add s hu hv hbd t r⟩
  by_cases had : a=d
  · subst d
    have hbc : b≠c := fun he => habne (hcommon a b hal hdm hbl (he.symm ▸ hcm))
    have hv' : UnitStep a c := by simpa only [UnitStep,IntegerGrid.manhattan_comm] using hv
    have he := common_source_distance_add s hu hv' hbc t (s-r)
    rw [← interpolate_reverse s c a (Nat.le_of_lt hr)] at he
    exact Or.inr ⟨a,hal,hdm,he⟩
  by_cases hbc : b=c
  · subst c
    have had : a≠d := fun he => habne (hcommon a b hal (he.symm ▸ hdm) hbl hcm)
    have hu' : UnitStep b a := by simpa only [UnitStep,IntegerGrid.manhattan_comm] using hu
    have he := common_source_distance_add s hu' hv had (s-t) r
    rw [← interpolate_reverse s a b (Nat.le_of_lt ht)] at he
    exact Or.inr ⟨b,hbl,hcm,he⟩
  by_cases hbd : b=d
  · subst d
    have hac : a≠c := fun he => habne (hcommon a b hal (he.symm ▸ hcm) hbl hdm)
    have hu' : UnitStep b a := by simpa only [UnitStep,IntegerGrid.manhattan_comm] using hu
    have hv' : UnitStep b c := by simpa only [UnitStep,IntegerGrid.manhattan_comm] using hv
    have he := common_source_distance_add s hu' hv' hac (s-t) (s-r)
    rw [← interpolate_reverse s a b (Nat.le_of_lt ht),
      ← interpolate_reverse s c b (Nat.le_of_lt hr)] at he
    exact Or.inr ⟨b,hbl,hdm,he⟩
  · exact Or.inl (interpolate_separation s hu hv hac had hbc hbd
      (Nat.le_of_lt ht) (Nat.le_of_lt hr))

/-- A distance below the dilation scale identifies the shared original
vertex and bounds both endpoint distances by the observed distance. -/
theorem subdivision_near_shared_vertex (s : Nat) (l m : List Point)
    (hl : l.IsChain UnitStep) (hm : m.IsChain UnitStep)
    (hcommon : ∀ u v, u ∈l → u ∈m → v ∈l → v ∈m → u =v)
    (p q : Point) (hp : p ∈subdivide s l) (hq : q ∈subdivide s m)
    (hnear : IntegerGrid.manhattan p q <s) :
    ∃ z, z∈l ∧ z∈m ∧
      IntegerGrid.manhattan (scale s z) p≤IntegerGrid.manhattan p q ∧
      IntegerGrid.manhattan (scale s z) q≤IntegerGrid.manhattan p q ∧
      IntegerGrid.manhattan p q=
        IntegerGrid.manhattan (scale s z) p+IntegerGrid.manhattan (scale s z) q := by
  rcases subdivision_distance_dichotomy s l m hl hm hcommon p q hp hq with hfar | ⟨z,hzl,hzm,he⟩
  · omega
  · exact ⟨z,hzl,hzm,by omega,by omega,he⟩

/-- Close points in bounded-width neighborhoods of two subdivided routes
are close to the same shared original vertex. This is the incidence-local
case used to rule out accidental contacts between compiled tentacles. -/
theorem subdivision_neighborhood_shared_vertex (s radius gap : Nat) (l m : List Point)
    (hl : l.IsChain UnitStep) (hm : m.IsChain UnitStep)
    (hcommon : ∀ u v, u ∈l → u ∈m → v ∈l → v ∈m → u =v)
    (p q u v : Point) (hp : p ∈subdivide s l) (hq : q ∈subdivide s m)
    (hpu : IntegerGrid.manhattan p u ≤radius) (hqv : IntegerGrid.manhattan q v ≤radius)
    (huv : IntegerGrid.manhattan u v ≤gap) (hsmall : 2 *radius +gap <s) :
    ∃ z, z∈l ∧ z∈m ∧
      IntegerGrid.manhattan (scale s z) u≤3*radius+gap ∧
      IntegerGrid.manhattan (scale s z) v≤3*radius+gap := by
  have ht1 := IntegerGrid.manhattan_triangle p u q
  have ht2 := IntegerGrid.manhattan_triangle u v q
  have hqv' : IntegerGrid.manhattan v q≤radius := by
    simpa only [IntegerGrid.manhattan_comm v q] using hqv
  have hpq : IntegerGrid.manhattan p q≤2*radius+gap := by omega
  obtain ⟨z,hzl,hzm,hzp,hzq,_⟩ := subdivision_near_shared_vertex s l m hl hm hcommon
    p q hp hq (by omega)
  have hzu := IntegerGrid.manhattan_triangle (scale s z) p u
  have hzv := IntegerGrid.manhattan_triangle (scale s z) q v
  exact ⟨z,hzl,hzm,by omega,by omega⟩

end GridHardness.LatticeRouteCore
