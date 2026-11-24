/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRegionBoundaries
public import GridHardness.SatCompleteArms
public import GridHardness.GridAssemblyGeometry

/-!
# SAT Complete Layout

Uniform, semantically constructed valid grid layouts for the actual
SAT bipartite graph. All six geometric validity fields are discharged;
no routing or clearance premise is left to the caller.
-/

@[expose] public section

namespace GridHardness.SatCompleteLayout
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
-- The proof normalizes the translated coordinates of the complete SAT layout.
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true
abbrev Vertex := SatBipartiteDrawing.Vertex

noncomputable instance vertexFintype (x : SatTy.denote) : Fintype (Vertex x) := Fintype.ofFinite _
noncomputable instance graphDecidable (x : SatTy.denote) : DecidableRel (SatBipartiteDrawing.graph x).Adj :=
  Classical.decRel _

noncomputable def body (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) : GridAssembly.Body :=
  if SatNineClusterPlacement.ownsTentacles x v then
    .star (SatNineClusterPlacement.frame x hw v) (SatCompleteArms.arms x hw v)
  else .cluster (SatNineClusterPlacement.frame x hw v)

noncomputable def layout (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) : GridAssembly.Layout (Vertex x) :=
  ⟨body x hw,SatCompletePorts.port x hw⟩

theorem body_valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) :
    (body x hw v).Valid := by
  unfold body
  split_ifs with hv
  · exact SatCompleteArms.arms_valid x hw v hv
  · trivial

theorem body_owner (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) :
    (body x hw v).ownsTentacles=SatNineClusterPlacement.ownsTentacles x v := by
  unfold body
  cases h : SatNineClusterPlacement.ownsTentacles x v <;> rfl

theorem body_points (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v : Vertex x) :
    (body x hw v).points=SatCompleteRegions.region x hw v := by
  apply Finset.ext
  intro p
  rw [SatCompleteRegions.mem_region]
  unfold body
  split_ifs with hv
  · exact SatCompleteArms.points_iff x hw v hv p
  · change p∈SatNineClusterPlacement.points x hw v ↔ _
    constructor
    · exact Or.inl
    · rintro (hp|⟨e,he,_⟩)
      · exact hp
      · have ho := (SatCollarCorridors.owners x e).1
        change SatNineClusterPlacement.ownsTentacles x (SatDockCorridors.owner x e)=true at ho
        rw [he] at ho
        exact False.elim (hv ho)

theorem body_port (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (v w : Vertex x)
    (hvw : (SatBipartiteDrawing.graph x).Adj v w) :
    (body x hw v).IsPort (SatCompletePorts.port x hw v w) := by
  obtain ⟨e,⟨ho,hr,hp,hq⟩|⟨ho,hr,hq,hp⟩⟩ := SatCompletePorts.adjacent_spec x hw v w hvw
  · have hv := (SatCollarCorridors.owners x e).1
    change SatNineClusterPlacement.ownsTentacles x (SatCompletePorts.owner x e)=true at hv
    rw [ho] at hv
    rw [body,ite_eq_left hv,hp]
    let i := SatOwnerIncidences.atOwnerVertex x v e ho
    exact ⟨SatClusterStubs.slot x v i,SatCompleteArms.arm_port x hw v hv i⟩
  · have hv := (SatCollarCorridors.owners x e).2
    change SatNineClusterPlacement.ownsTentacles x (SatCompletePorts.recipient x e)=false at hv
    rw [hr] at hv
    rw [body,hv]
    exact ⟨SatCompleteTentacles.side x hw e,hp⟩

/-- Every well-formed source formula receives a complete valid grid layout. -/
theorem valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    (layout x hw).Valid (SatBipartiteDrawing.graph x) := by
  classical
  refine ⟨body_valid x hw,?_,?_,body_port x hw,SatCompletePorts.distinctPorts x hw,?_⟩
  · intro v w hvw
    change Disjoint (body x hw v).points (body x hw w).points
    rw [body_points,body_points]
    exact SatCompleteRegions.disjoint x hw v w hvw
  · intro v w hvw
    change (body x hw v).ownsTentacles≠(body x hw w).ownsTentacles
    rw [body_owner,body_owner]
    exact SatNineClusterPlacement.opposite_owners x v w hvw
  · intro v w hvw
    change TwoClusterAssembly.boundary (body x hw v).points (body x hw w).points = _
    rw [body_points,body_points]
    exact SatCompleteRegions.boundary x hw v w hvw

end GridHardness.SatCompleteLayout
