/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCompleteRegions
public import GridHardness.SatCompletePorts

/-!
# SAT Region Boundaries

Exact singleton boundaries for all adjacent regions of the actual SAT
construction, and empty boundaries for every nonadjacent pair.
-/

@[expose] public section

namespace GridHardness.SatCompleteRegions
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
open SatCompleteTentacles
open SatCompletePorts (port adjacent_spec port_owner port_recipient)
set_option autoImplicit false
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true

attribute [local instance] Classical.propDecidable

local instance regionsBoundaryAdjDecidable : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q=1))

theorem port_mem (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v w : Vertex x)
    (hvw : (SatBipartiteDrawing.graph x).Adj v w) : port x hw v w∈region x hw v := by
  obtain ⟨e,⟨ho,hr,hp,_⟩|⟨ho,hr,_,hp⟩⟩ := adjacent_spec x hw v w hvw
  · rw [hp,← ho]
    exact drawing_subset x hw e ((drawing x hw e).tip_mem (valid x hw e) 0)
  · rw [hp]
    exact cluster_subset x hw v (SatNineClusterPlacement.corner_mem x hw v _)

theorem port_adjacent (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v w : Vertex x)
    (hvw : (SatBipartiteDrawing.graph x).Adj v w) : lattice.Adj (port x hw v w) (port x hw w v) := by
  obtain ⟨e,⟨ho,hr,hp,hq⟩|⟨ho,hr,hq,hp⟩⟩ := adjacent_spec x hw v w hvw
  · rw [hp,hq,← hr]
    exact (between x hw e).tip_adjacent
  · rw [hp,hq,← hr]
    exact (between x hw e).tip_adjacent.symm

/-- Every cross-region lattice edge equals the canonical graph port pair. -/
theorem adjacent_ports_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v w : Vertex x) (hvw : v ≠w) (p q : Point)
    (hp : p ∈region x hw v) (hq : q ∈region x hw w) :
    lattice.Adj p q ↔ (SatBipartiteDrawing.graph x).Adj v w ∧
      p=port x hw v w ∧ q=port x hw w v := by
  constructor
  · intro ha
    rcases (adjacent_iff x hw v w hvw p q hp hq).mp ha with
      ⟨e,ho,hr,hp',hq'⟩|⟨e,ho,hr,hq',hp'⟩
    · subst v; subst w
      exact ⟨SatCollarCorridors.endpoints_adj x e,
        hp'.trans (port_owner x hw e).symm,hq'.trans (port_recipient x hw e).symm⟩
    · subst w; subst v
      exact ⟨(SatCollarCorridors.endpoints_adj x e).symm,
        hp'.trans (port_recipient x hw e).symm,hq'.trans (port_owner x hw e).symm⟩
  · rintro ⟨ha,rfl,rfl⟩
    exact port_adjacent x hw v w ha

theorem boundary (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v w : Vertex x) (hvw : v ≠w) :
    TwoClusterAssembly.boundary (region x hw v) (region x hw w) =
      if (SatBipartiteDrawing.graph x).Adj v w then {(port x hw v w,port x hw w v)} else ∅ := by
  classical
  by_cases ha : (SatBipartiteDrawing.graph x).Adj v w
  · rw [ite_eq_left ha]
    apply TwoClusterAssembly.boundary_eq_singleton (port_mem x hw v w ha) (port_mem x hw w v ha.symm)
    intro p hp q hq
    rw [adjacent_ports_iff x hw v w hvw p q hp hq]
    simp only [ha,true_and]
  · rw [ite_eq_right ha]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hp,hq,hpq⟩ := (TwoClusterAssembly.mem_boundary _ _ z.1 z.2).mp hz
    exact ha ((adjacent_ports_iff x hw v w hvw z.1 z.2 hp hq).mp hpq).1

end GridHardness.SatCompleteRegions
