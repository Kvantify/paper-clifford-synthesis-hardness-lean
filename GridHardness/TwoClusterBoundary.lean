/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TwoClusterAssembly

/-!
# Two Cluster Boundary

Membership and finite-union laws for actual lattice boundaries.
-/

@[expose] public section

namespace GridHardness.TwoClusterAssembly
open CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false

local instance boundaryAdjDecidable : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q=1))

theorem mem_boundary (S T : Finset Point) (p q : Point) :
    (p,q)∈boundary S T ↔ p∈S ∧ q∈T ∧ lattice.Adj p q := by
  simp only [boundary,Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product,and_assoc]

theorem boundary_union_right (S T U : Finset Point) :
    boundary S (T∪U)=boundary S T ∪ boundary S U := by
  simp only [boundary,Finset.product_eq_sprod,Finset.product_union,Finset.filter_union]

theorem boundary_union_left (S T U : Finset Point) :
    boundary (S∪T) U=boundary S U ∪ boundary T U := by
  simp only [boundary,Finset.product_eq_sprod,Finset.union_product,Finset.filter_union]

theorem boundary_empty_of_nonadjacent (S T : Finset Point)
    (h : ∀ p∈S, ∀ q∈T, ¬lattice.Adj p q) : boundary S T=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hm := (mem_boundary S T z.1 z.2).mp hz
  exact h z.1 hm.1 z.2 hm.2.1 hm.2.2

end GridHardness.TwoClusterAssembly
