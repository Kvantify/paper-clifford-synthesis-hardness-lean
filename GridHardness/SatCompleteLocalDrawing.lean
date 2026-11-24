/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCompleteTentacles
public import GridHardness.SignedTentacleLocalDocking

/-!
# SAT Complete Local Drawing

Complete edge tentacles in their owning cluster's local coordinates.
Every added strip is proved clear of that cluster, giving the recursive
certificate required for local Hamiltonian routing through a star.
-/

@[expose] public section

namespace GridHardness.SatCompleteTentacles
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

noncomputable def localDrawing (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Drawing :=
  Drawing.transform (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e)).inverse
    (drawing x hw e)

theorem localDrawing_valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (localDrawing x hw e).Valid := Drawing.transform_valid _ _ (valid x hw e)

@[simp] theorem localDrawing_placed (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    Drawing.transform (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e))
      (localDrawing x hw e)=drawing x hw e := Drawing.transform_inverse _ _

theorem localDrawing_points (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (localDrawing x hw e).points.image
      (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e)).map =
        (drawing x hw e).points := by
  rw [← Drawing.transform_points,localDrawing_placed]

theorem baseFrame (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).baseFrame =
      (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e)).comp
        (NineClusterAttachment.dock true (SatDockCorridors.side x hw e false)) := by
  rw [drawing,TerminalCollarAttach.attach_eq_graft,Drawing.graft_baseFrame]
  exact RunChain.compile_baseFrame _ _ _

theorem tailPoints (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).tailPoints=(SatOwnerTentacles.drawing x hw e).tailPoints∪tail x hw e := by
  rw [drawing,TerminalCollarAttach.attach_eq_graft,Drawing.graft_tailPoints,
    Drawing.transform_tailPoints]
  rfl

set_option maxHeartbeats 800000 in
-- The geometric bound combines the coordinates of the two route endpoints.
theorem owner_tail_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (p : Point) (hp : p ∈(SatOwnerTentacles.drawing x hw e).tailPoints) :
    48≤IntegerGrid.manhattan
      ((SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e)).map (1,1)) p := by
  have h := CardinalRunChain.compile_tail_distance (SatOwnerTentacles.state x hw e)
    (SatOwnerTentacles.firstRun x hw e).2 (SatOwnerTentacles.remaining x hw e)
    64 52 (SatOwnerTentacles.directions x hw e) (SatOwnerTentacles.indexSeparated x hw e)
    (SatOwnerTentacles.lengths x hw e) p hp
  have hd := NineClusterOwnerRun.state_start_distance
    (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e))
    (SatDockCorridors.side x hw e false)
  have htri := IntegerGrid.manhattan_triangle ((SatOwnerTentacles.state x hw e).point 0)
    ((SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e)).map (1,1)) p
  rw [IntegerGrid.manhattan_comm ((SatOwnerTentacles.state x hw e).point 0)
    ((SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e)).map (1,1))] at htri
  change IntegerGrid.manhattan _ ((SatOwnerTentacles.state x hw e).point 0)=2 at hd
  norm_num only [min_eq_right (by decide : 52≤64)] at h
  omega

theorem localDrawing_docked (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    NineClusterAttachment.Docked true (SatDockCorridors.side x hw e false) (localDrawing x hw e) := by
  apply Drawing.local_docked _ _ _ (baseFrame x hw e)
  intro p hp
  rw [tailPoints] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact le_trans (by decide : 4≤48) (owner_tail_distance x hw e p hp)
  · have hc : (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e)).map (1,1) ∈
        SatNineClusterPlacement.points x hw (SatDockCorridors.owner x e) := by
      apply Finset.mem_image.mpr
      exact ⟨(1,1),by decide,rfl⟩
    exact le_trans (by decide : 4≤47) (tail_cluster_distance x hw e _
      (SatDockCorridors.owner_recipient_ne x e e) _ p hc hp)

end GridHardness.SatCompleteTentacles
