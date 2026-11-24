/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteSubdivision

/-!
# Lattice Route Separation

Quantitative separation after subdivision. Original disjoint lattice
paths have distance at least the dilation factor, including their endpoints.
These estimates are the margins needed for later local gadget insertion.
-/

public section

namespace GridHardness.LatticeSubdivision
open CliffordSynthesis
set_option autoImplicit false

theorem manhattan_pos_of_ne {p q : Point} (h : p ≠q) :
    0<IntegerGrid.manhattan p q := by
  have hn : p.1≠q.1 ∨ p.2≠q.2 := by
    by_contra h'
    push Not at h'
    exact h (Prod.ext h'.1 h'.2)
  dsimp [IntegerGrid.manhattan]
  omega

theorem scale_separation (s : Nat) {p q : Point} (h : p ≠q) :
    s≤IntegerGrid.manhattan (scale s p) (scale s q) := by
  rw [scale_manhattan]
  exact Nat.le_mul_of_pos_right s (manhattan_pos_of_ne h)

/-- A vertex not on the original route is separated from every point
of the subdivided route by at least the scale. -/
theorem subdivide_vertex_clearance (s : Nat) (l : List Point)
    (hc : l.IsChain UnitStep) (v : Point) (hv : v ∉l)
    (q : Point) (hq : q ∈subdivide s l) :
    s≤IntegerGrid.manhattan q (scale s v) := by
  rcases (subdivide_mem s l q).mp hq with ⟨a,ha,rfl⟩ | ⟨a,b,hab,t,ht,rfl⟩
  · exact scale_separation s (fun he => hv (he ▸ List.mem_of_getLast? ha))
  · have hm := edges_mem_vertices l a b hab
    exact interpolate_vertex_separation s (z:=v) (edges_unit l hc a b hab)
      (fun he => hv (he ▸ hm.1)) (fun he => hv (he ▸ hm.2)) (Nat.le_of_lt ht)

/-- Two disjoint original routes retain a full scale-width gap after
every unit step has been subdivided. -/
theorem subdivide_disjoint_clearance (s : Nat) (l m : List Point)
    (hl : l.IsChain UnitStep) (hm : m.IsChain UnitStep) (hd : List.Disjoint l m)
    (p q : Point) (hp : p ∈subdivide s l) (hq : q ∈subdivide s m) :
    s≤IntegerGrid.manhattan p q := by
  rcases (subdivide_mem s l p).mp hp with ⟨a,ha,rfl⟩ | ⟨a,b,hab,t,ht,rfl⟩
  · rw [IntegerGrid.manhattan_comm]
    exact subdivide_vertex_clearance s m hm a
      (fun h => hd (List.mem_of_getLast? ha) h) q hq
  · rcases (subdivide_mem s m q).mp hq with ⟨u,hu,rfl⟩ | ⟨u,v,huv,r,hr,rfl⟩
    · exact subdivide_vertex_clearance s l hl u
        (fun h => hd h (List.mem_of_getLast? hu)) _
        ((subdivide_mem s l _).mpr (Or.inr ⟨a,b,hab,t,ht,rfl⟩))
    · have habm := edges_mem_vertices l a b hab
      have huvm := edges_mem_vertices m u v huv
      exact interpolate_separation s (edges_unit l hl a b hab) (edges_unit m hm u v huv)
        (fun he => hd (he ▸ habm.1) huvm.1)
        (fun he => hd (he ▸ habm.1) huvm.2)
        (fun he => hd (he ▸ habm.2) huvm.1)
        (fun he => hd (he ▸ habm.2) huvm.2)
        (Nat.le_of_lt ht) (Nat.le_of_lt hr)

end GridHardness.LatticeSubdivision
