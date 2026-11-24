/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCorridorTentacles
public import GridHardness.SatClusterStubs
public import GridHardness.TerminalCollarMatched

/-!
# SAT Receiving Collars

Receiving collars at the SAT graph vertices. Their radius-sixteen
entries agree with the corridor endpoints. Collars have exact recipient
boundaries and are separated at distinct vertices and from nonincident
corridors. `SatCompleteTentacles` joins them to owner-to-recipient strip chains.
-/

@[expose] public section

namespace GridHardness.SatReceivingCollars
open CliffordComplexity CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Vertex := SatBipartiteDrawing.Vertex
abbrev Edge := SatBipartiteDrawing.Edge

noncomputable def translation (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) : Frame := ⟨true,false,false,SatNineClusterPlacement.anchor x hw v⟩

noncomputable def drawing (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (s : Fin 4) (b : Bool) : Drawing :=
  Drawing.transform (translation x hw v) (TerminalCollarMatched.phaseDrawing s b)

theorem valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (s : Fin 4) (b : Bool) : (drawing x hw v s b).Valid :=
  Drawing.transform_valid _ _ (TerminalCollarMatched.phase_valid s b)

theorem frame_eq (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (hv : SatNineClusterPlacement.color x v =1) :
    (translation x hw v).comp TerminalCollar.clusterFrame=SatNineClusterPlacement.frame x hw v := by
  simp [translation,SatNineClusterPlacement.frame,SatNineClusterPlacement.anchor,
    NineClusterPlacement.frame,Frame.comp,TerminalCollar.clusterFrame,Frame.map,place,sign,
    LatticeSubdivision.scale,hv,sub_eq_add_neg]

/-- The incoming lane on the ideal axis depends on the transverse phase. -/
def axisLane (b : Bool) : Fin 2 := if b then 1 else 0

theorem local_start_axis (d : Fin 4) (b : Bool) :
    (TerminalCollarMatched.phaseDrawing (NineClusterDockGeometry.sideOfDirection d) b).start
      (axisLane b)=DirectedLocalLayout.ray d 16 := by
  rw [TerminalCollarMatched.phase_start_coordinates]
  fin_cases d <;> cases b <;> rfl

theorem start_axis (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (t b : Bool) :
    (drawing x hw (SatBipartiteDirections.endpointVertex x e t)
      (NineClusterDockGeometry.sideOfDirection (SatBipartiteDirections.direction x hw e t)) b).start
      (axisLane b)=SatCollarCorridorCore.endpoint x hw e t := by
  rw [drawing,Drawing.transform_start,local_start_axis]
  simp [translation,Frame.map,place,sign,SatCollarCorridorCore.endpoint,
    SatCollarCorridorCore.anchor,SatNineClusterPlacement.anchor]

/-- The exact induced boundary contains only the selected target edge. -/
theorem boundary_singleton (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (hv : SatNineClusterPlacement.color x v =1) (s : Fin 4) (b : Bool) :
    TwoClusterAssembly.boundary (SatNineClusterPlacement.points x hw v)
      (drawing x hw v s b).points =
      {(SatNineClusterPlacement.corner x hw v s,(drawing x hw v s b).tip 0)} := by
  change TwoClusterAssembly.boundary (TwoClusterAssembly.cluster (SatNineClusterPlacement.frame x hw v))
    (drawing x hw v s b).points =
    {(TwoClusterAssembly.corner (SatNineClusterPlacement.frame x hw v) s,_)}
  rw [← frame_eq x hw v hv,drawing,TwoClusterAssembly.cluster_comp,Drawing.transform_points,
    TwoClusterAssembly.boundary_transform,TerminalCollarMatched.phase_boundary_singleton,
    Finset.image_singleton,TwoClusterAssembly.corner_comp,Drawing.transform_tip]

theorem cluster_disjoint (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (hv : SatNineClusterPlacement.color x v =1) (s : Fin 4) (b : Bool) :
    Disjoint (SatNineClusterPlacement.points x hw v) (drawing x hw v s b).points := by
  change Disjoint (TwoClusterAssembly.cluster (SatNineClusterPlacement.frame x hw v)) _
  rw [← frame_eq x hw v hv,TwoClusterAssembly.cluster_comp,drawing,Drawing.transform_points]
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
  have hu' := ((translation x hw v).map_mem_image u _).mp hq
  exact Finset.disjoint_left.mp (TerminalCollarMatched.phase_cluster_disjoint s b) hu hu'

theorem radius (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (s : Fin 4) (b : Bool) (p : Point)
    (hp : p ∈(drawing x hw v s b).points) :
    IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw v) p≤17 := by
  rw [drawing,Drawing.transform_points] at hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have h := TerminalCollarMatched.phase_radius s b q hq
  have hd := (translation x hw v).distance (0,0) q
  rw [Frame.map_zero] at hd
  exact hd.trans_le h

theorem card_le (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (s : Fin 4) (b : Bool) : (drawing x hw v s b).points.card≤50 := by
  rw [drawing,Drawing.transform_points,Finset.card_image_of_injective _ (translation x hw v).injective]
  exact TerminalCollarMatched.phase_card_le s b

/-- All lane choices on different sides of one recipient remain separated. -/
theorem same_vertex_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (s t : Fin 4) (b c : Bool) (hst : s ≠t) (p q : Point)
    (hp : p ∈(drawing x hw v s b).points) (hq : q ∈(drawing x hw v t c).points) :
    3≤IntegerGrid.manhattan p q := by
  rw [drawing,Drawing.transform_points] at hp hq
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨w,hw',rfl⟩ := Finset.mem_image.mp hq
  rw [(translation x hw v).distance]
  exact TerminalCollarMatched.phase_distance s t b c hst u hu w hw'

/-- Collars at distinct actual vertices have a thirty-step margin. -/
theorem different_vertex_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v w : Vertex x) (hvw : v ≠w) (s t : Fin 4) (b c : Bool) (p q : Point)
    (hp : p ∈(drawing x hw v s b).points) (hq : q ∈(drawing x hw w t c).points) :
    30≤IntegerGrid.manhattan p q := by
  have hp' := radius x hw v s b p hp
  have hq' := radius x hw w t c q hq
  have hd := LatticeSubdivision.scale_separation 64
    (fun he => hvw (SatBipartiteDrawing.point_injective x hw he))
  change 64≤IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw v)
    (SatNineClusterPlacement.anchor x hw w) at hd
  have h1 := IntegerGrid.manhattan_triangle (SatNineClusterPlacement.anchor x hw v) p
    (SatNineClusterPlacement.anchor x hw w)
  have h2 := IntegerGrid.manhattan_triangle p q (SatNineClusterPlacement.anchor x hw w)
  rw [IntegerGrid.manhattan_comm q (SatNineClusterPlacement.anchor x hw w)] at h2
  omega

/-- A receiving collar avoids every unrelated cluster body. -/
theorem other_cluster_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v w : Vertex x) (hvw : v ≠w) (s : Fin 4) (b : Bool) (p q : Point)
    (hp : p ∈(drawing x hw v s b).points) (hq : q ∈SatNineClusterPlacement.points x hw w) :
    44≤IntegerGrid.manhattan p q := by
  have hp' := radius x hw v s b p hp
  have hq' := SatNineClusterPlacement.radius x hw w q hq
  have hd := LatticeSubdivision.scale_separation 64
    (fun he => hvw (SatBipartiteDrawing.point_injective x hw he))
  change 64≤IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw v)
    (SatNineClusterPlacement.anchor x hw w) at hd
  have h1 := IntegerGrid.manhattan_triangle (SatNineClusterPlacement.anchor x hw v) p
    (SatNineClusterPlacement.anchor x hw w)
  have h2 := IntegerGrid.manhattan_triangle p q (SatNineClusterPlacement.anchor x hw w)
  rw [IntegerGrid.manhattan_comm q (SatNineClusterPlacement.anchor x hw w)] at h2
  omega

/-- Nonincident corridor cores retain forty-seven steps of clearance. -/
theorem unrelated_corridor_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (s : Fin 4) (b : Bool) (e : Edge x)
    (hv : v ≠SatBipartiteDrawing.source x e) (ht : v ≠SatBipartiteDrawing.target x e)
    (p q : Point) (hp : p ∈(drawing x hw v s b).points) (hq : q ∈SatCollarCorridors.route x hw e) :
    47≤IntegerGrid.manhattan p q := by
  have hp' := radius x hw v s b p hp
  have hq' := SatCollarCorridorCore.unrelated_anchor_clearance x hw e v hv ht q
    ((SatCollarCorridors.mem_route x hw e q).mp hq)
  have h := IntegerGrid.manhattan_triangle (SatNineClusterPlacement.anchor x hw v) p q
  change 64≤IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw v) q at hq'
  omega

/-- The same estimate includes the actual two-unit-thick central construction. -/
theorem unrelated_tentacle_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) (s : Fin 4) (b : Bool) (e : Edge x)
    (hv : v ≠SatBipartiteDrawing.source x e) (ht : v ≠SatBipartiteDrawing.target x e)
    (p q : Point) (hp : p ∈(drawing x hw v s b).points)
    (hq : q ∈(SatCorridorTentacles.drawing x hw e).points) :
    45≤IntegerGrid.manhattan p q := by
  obtain ⟨r,hr,hqr⟩ := SatCorridorTentacles.centerline_distance x hw e q hq
  have hd := unrelated_corridor_distance x hw v s b e hv ht p r hp hr
  have h := IntegerGrid.manhattan_triangle p q r
  omega

/-- The actual nonowning endpoint has the phase used by the receiving template. -/
theorem recipient_color (x : SatTy.denote) (e : Edge x) :
    SatNineClusterPlacement.color x (SatCollarCorridors.endVertex x e)=1 := by
  have ho := (SatCollarCorridors.owners x e).2
  have hn : SatNineClusterPlacement.color x (SatCollarCorridors.endVertex x e)≠0 :=
    of_decide_eq_false ho
  apply Fin.ext
  have hlt := (SatNineClusterPlacement.color x (SatCollarCorridors.endVertex x e)).isLt
  have hne : (SatNineClusterPlacement.color x (SatCollarCorridors.endVertex x e)).val≠0 :=
    fun he => hn (Fin.ext he)
  simp only [Fin.val_one]
  omega

noncomputable def side (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) : Fin 4 :=
  NineClusterDockGeometry.sideOfDirection
    (SatBipartiteDirections.direction x hw e (!(SatCollarCorridors.reverseEdge x e)))

noncomputable def receiver (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) : Drawing :=
  drawing x hw (SatCollarCorridors.endVertex x e) (side x hw e) b

theorem receiver_valid (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) : (receiver x hw e b).Valid := valid _ _ _ _ _

/-- The selected axis lane is exactly the owner-oriented corridor's final point. -/
theorem receiver_entry (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) :
    (receiver x hw e b).start (axisLane b)=SatCollarCorridors.endPoint x hw e :=
  start_axis x hw e (!(SatCollarCorridors.reverseEdge x e)) b

theorem receiver_boundary (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) :
    TwoClusterAssembly.boundary
      (SatNineClusterPlacement.points x hw (SatCollarCorridors.endVertex x e))
      (receiver x hw e b).points =
      {(SatNineClusterPlacement.corner x hw (SatCollarCorridors.endVertex x e) (side x hw e),
        (receiver x hw e b).tip 0)} :=
  boundary_singleton x hw _ (recipient_color x e) _ b

/-- Actual incidences at the same recipient use distinct collar sides. -/
theorem receiver_sides_ne (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f)
    (hv : SatCollarCorridors.endVertex x e =SatCollarCorridors.endVertex x f) :
    side x hw e≠side x hw f := by
  let i : SatBipartiteDirections.Incidence x (SatCollarCorridors.endVertex x e) :=
    ⟨(e,!(SatCollarCorridors.reverseEdge x e)),rfl⟩
  let j : SatBipartiteDirections.Incidence x (SatCollarCorridors.endVertex x e) :=
    ⟨(f,!(SatCollarCorridors.reverseEdge x f)),hv.symm⟩
  intro h
  have hs : SatClusterStubs.side x hw _ i=SatClusterStubs.side x hw _ j := h
  have hij := SatClusterStubs.side_injective x hw _ hs
  exact hef (congrArg (fun k => k.val.1) hij)

/-- All actual receiving collars are mutually separated, including those
that share a recipient; the lane choices can be made independently. -/
theorem receiver_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (b c : Bool) (p q : Point)
    (hp : p ∈(receiver x hw e b).points) (hq : q ∈(receiver x hw f c).points) :
    3≤IntegerGrid.manhattan p q := by
  by_cases hv : SatCollarCorridors.endVertex x e=SatCollarCorridors.endVertex x f
  · have hs := receiver_sides_ne x hw e f hef hv
    have hp' : p∈(drawing x hw (SatCollarCorridors.endVertex x f) (side x hw e) b).points := by
      simpa only [receiver,hv] using hp
    exact same_vertex_distance x hw _ _ _ b c hs p q hp' hq
  · have hd := different_vertex_distance x hw _ _ hv _ _ b c p q hp hq
    omega

end GridHardness.SatReceivingCollars
