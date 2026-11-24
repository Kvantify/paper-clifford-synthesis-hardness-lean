/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatOwnerTentacles
public import GridHardness.SatReceivingCollars
public import GridHardness.SatDockCorridorSeparation
public import GridHardness.TerminalCollarAttach
public import GridHardness.TwoClusterBoundary

/-!
# SAT Complete Tentacles

Complete signed tentacles for every edge of the actual SAT graph.
The owner dock, long middle chain, and phase-selected recipient collar
are joined with their exact induced boundary edges proved.
-/

@[expose] public section

namespace GridHardness.SatCompleteTentacles
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
-- The geometric proof unfolds the coordinates of the constructed routes.
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true

local instance completeAdjDecidable : DecidableRel lattice.Adj := fun p q => inferInstanceAs
  (Decidable (IntegerGrid.manhattan p q=1))

abbrev Edge := SatDockCorridors.Edge
abbrev Vertex := SatDockCorridors.Vertex

noncomputable def anchor (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Point :=
  SatNineClusterPlacement.anchor x hw (SatDockCorridors.recipient x e)
noncomputable def side (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Fin 4 :=
  SatDockCorridors.side x hw e true
noncomputable def lane (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Fin 2 :=
  (SatOwnerTentacles.terminalState x hw e).lane
noncomputable def phase (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Bool :=
  TerminalCollarAttach.phase (anchor x hw e) (SatOwnerTentacles.drawing x hw e)
    (side x hw e) (lane x hw e)
noncomputable def tail (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Finset Point :=
  (TerminalCollarMatched.tail (side x hw e) (phase x hw e)).image
    (TerminalCollarAttach.shift (anchor x hw e)).map
noncomputable def drawing (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Drawing :=
  TerminalCollarAttach.attach (anchor x hw e) (SatOwnerTentacles.drawing x hw e)
    (side x hw e) (lane x hw e)

theorem endPoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    SatDockCorridors.endPoint x hw e =
      (TerminalCollarAttach.shift (anchor x hw e)).map (TerminalCollarMatch.innerPoint (side x hw e)) := by
  unfold SatDockCorridors.endPoint SatDockCorridors.pointAt
  simp only [SatDockCorridors.endpointVertex, ite_true]
  unfold SatDockCorridors.endCut side SatDockCorridors.side
  generalize SatDockCorridors.direction x hw e true=d
  fin_cases d <;> simp [NineClusterDockGeometry.sideOfDirection, DirectedLocalLayout.ray,
    TerminalCollarMatch.innerPoint, TerminalCollarAttach.shift, Frame.map, place, sign, anchor]

theorem aligned_tip (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (SatOwnerTentacles.drawing x hw e).tip (lane x hw e) =
      (TerminalCollarAttach.shift (anchor x hw e)).map (TerminalCollarMatch.innerPoint (side x hw e)) :=
  (SatOwnerTentacles.tip x hw e).trans (endPoint x hw e)

theorem locality (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    TerminalCollarAttach.BoxLocality (anchor x hw e) (SatOwnerTentacles.drawing x hw e) := by
  apply TerminalCollarAttach.boxLocality_of_close _ _ (side x hw e)
  intro p hp hc
  rw [← endPoint] at hc
  exact SatOwnerTentacles.last_strip_of_close x hw e p hp hc

theorem valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).Valid :=
  TerminalCollarAttach.valid _ _ _ _ (SatOwnerTentacles.valid x hw e)
    (SatOwnerTentacles.endframe_direction x hw e) (aligned_tip x hw e) (locality x hw e)

theorem start (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) (r : Fin 2) :
    (drawing x hw e).start r = (SatOwnerTentacles.drawing x hw e).start r :=
  TerminalCollarAttach.start _ _ _ _ r

theorem tip (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) (r : Fin 2) :
    (drawing x hw e).tip r =
      (TerminalCollarAttach.shift (anchor x hw e)).map (TerminalCollarRotations.tip (side x hw e) r) :=
  TerminalCollarAttach.tip _ _ _ _ r

theorem points (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).points = (SatOwnerTentacles.drawing x hw e).points ∪ tail x hw e :=
  TerminalCollarAttach.points _ _ _ _

theorem card_le (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (drawing x hw e).points.card ≤ (SatOwnerTentacles.drawing x hw e).points.card + 34 :=
  TerminalCollarAttach.card_le _ _ _ _ (SatOwnerTentacles.valid x hw e)
    (SatOwnerTentacles.endframe_direction x hw e) (aligned_tip x hw e) (locality x hw e)

theorem recipient_frame (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (TerminalCollarAttach.shift (anchor x hw e)).comp TerminalCollar.clusterFrame =
      SatNineClusterPlacement.frame x hw (SatDockCorridors.recipient x e) :=
  SatReceivingCollars.frame_eq x hw _ (SatReceivingCollars.recipient_color x e)

theorem recipient_disjoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    Disjoint (SatNineClusterPlacement.points x hw (SatDockCorridors.recipient x e))
      (drawing x hw e).points := by
  have h := TerminalCollarAttach.cluster_disjoint _ _ _ _
    (SatOwnerTentacles.endframe_direction x hw e) (aligned_tip x hw e) (locality x hw e)
  rw [recipient_frame] at h
  exact h

theorem recipient_boundary (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    TwoClusterAssembly.boundary (SatNineClusterPlacement.points x hw (SatDockCorridors.recipient x e))
      (drawing x hw e).points =
        {(SatNineClusterPlacement.corner x hw (SatDockCorridors.recipient x e) (side x hw e),
          (drawing x hw e).tip 0)} := by
  have h := TerminalCollarAttach.boundary _ _ _ _ (SatOwnerTentacles.valid x hw e)
    (SatOwnerTentacles.endframe_direction x hw e) (aligned_tip x hw e) (locality x hw e)
  rw [recipient_frame] at h
  exact h

theorem tail_radius (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (p : Point) (hp : p ∈tail x hw e) : IntegerGrid.manhattan (anchor x hw e) p≤14 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hd := (TerminalCollarAttach.shift (anchor x hw e)).distance (0,0) q
  rw [Frame.map_zero] at hd
  exact hd.trans_le (TerminalCollarMatched.tail_radius _ _ q hq)

/-- New receiving strips stay far from every cluster except their recipient. -/
theorem tail_cluster_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (v : Vertex x) (hv : v ≠SatDockCorridors.recipient x e) (p q : Point)
    (hp : p ∈SatNineClusterPlacement.points x hw v) (hq : q ∈tail x hw e) :
    47≤IntegerGrid.manhattan p q := by
  have hp' := SatNineClusterPlacement.radius x hw v p hp
  have hq' := tail_radius x hw e q hq
  have hd := LatticeSubdivision.scale_separation 64
    (fun he => hv (SatBipartiteDrawing.point_injective x hw he))
  change 64≤IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw v) (anchor x hw e) at hd
  have h1 := IntegerGrid.manhattan_triangle (SatNineClusterPlacement.anchor x hw v) p (anchor x hw e)
  have h2 := IntegerGrid.manhattan_triangle p q (anchor x hw e)
  rw [IntegerGrid.manhattan_comm q (anchor x hw e)] at h2
  omega

theorem owner_disjoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    Disjoint (SatNineClusterPlacement.points x hw (SatDockCorridors.owner x e))
      (drawing x hw e).points := by
  rw [points]
  apply Finset.disjoint_union_right.mpr
  refine ⟨(SatOwnerTentacles.owner_interface x hw e).1, Finset.disjoint_left.mpr ?_⟩
  intro p hp hq
  have h := tail_cluster_distance x hw e _ (SatDockCorridors.owner_recipient_ne x e e) p p hp hq
  simp [IntegerGrid.manhattan] at h

theorem owner_boundary (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    TwoClusterAssembly.boundary (SatNineClusterPlacement.points x hw (SatDockCorridors.owner x e))
      (drawing x hw e).points =
        {(SatNineClusterPlacement.corner x hw (SatDockCorridors.owner x e) (SatDockCorridors.side x hw e false),
          (drawing x hw e).start 0),
         (TwoClusterAssembly.mate (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e))
          (SatDockCorridors.side x hw e false), (drawing x hw e).start 1)} := by
  rw [start, start, ← (SatOwnerTentacles.owner_interface x hw e).2,points]
  rw [TwoClusterAssembly.boundary_union_right]
  have he : TwoClusterAssembly.boundary
      (SatNineClusterPlacement.points x hw (SatDockCorridors.owner x e)) (tail x hw e)=∅ := by
    apply TwoClusterAssembly.boundary_empty_of_nonadjacent
    intro p hp q hq ha
    have hd := tail_cluster_distance x hw e _ (SatDockCorridors.owner_recipient_ne x e e) p q hp hq
    change IntegerGrid.manhattan p q=1 at ha
    omega
  rw [he,Finset.union_empty]

/-- Both endpoint interfaces hold for the complete, actual edge drawing. -/
theorem between (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    TwoClusterAssembly.Between (drawing x hw e)
      (SatNineClusterPlacement.frame x hw (SatDockCorridors.owner x e))
      (SatNineClusterPlacement.frame x hw (SatDockCorridors.recipient x e))
      (SatDockCorridors.side x hw e false) (side x hw e) :=
  ⟨owner_disjoint x hw e, recipient_disjoint x hw e,
    SatNineClusterPlacement.points_disjoint x hw _ _ (SatDockCorridors.owner_recipient_ne x e e),
    (fun p hp q hq => SatNineClusterPlacement.points_nonadjacent x hw _ _
      (SatDockCorridors.owner_recipient_ne x e e) p q hp hq),
    owner_boundary x hw e, recipient_boundary x hw e⟩

end GridHardness.SatCompleteTentacles
