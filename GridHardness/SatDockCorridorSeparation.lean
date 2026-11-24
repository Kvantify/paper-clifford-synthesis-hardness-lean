/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatDockCorridors
public import GridHardness.LatticeRouteNearIntersection

/-!
# SAT Dock Corridor Separation

Cross-corridor localization for the actual asymmetric dock routes.
Any contact between their width-two neighborhoods must occur near a shared
graph vertex; unrelated graph vertices retain the full dilation margin.
-/

public section

namespace GridHardness.SatDockCorridors
open CliffordComplexity CliffordSynthesis LatticeRouteDirections
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Reorientation preserves the unordered pair of incident graph vertices. -/
theorem incident_iff (x : SatTy.denote) (e : Edge x) (v : Vertex x) :
    (v=owner x e ∨ v=recipient x e) ↔
      (v=SatBipartiteDrawing.source x e ∨ v=SatBipartiteDrawing.target x e) := by
  unfold owner recipient SatCollarCorridors.startVertex SatCollarCorridors.endVertex
    SatBipartiteDirections.endpointVertex
  cases h : SatCollarCorridors.reverseEdge x e <;> simp [or_comm]

/-- A shared graph vertex has the same owning role for both incident edges;
it can never be an owner for one edge and a recipient for the other. -/
theorem shared_endpoint_roles (x : SatTy.denote) (e f : Edge x) (v : Vertex x)
    (he : v =owner x e ∨ v =recipient x e) (hf : v =owner x f ∨ v =recipient x f) :
    (v=owner x e ∧ v=owner x f) ∨ (v=recipient x e ∧ v=recipient x f) := by
  have heown := SatCollarCorridors.owners x e
  have hfown := SatCollarCorridors.owners x f
  rcases he with he | he <;> rcases hf with hf | hf
  · exact Or.inl ⟨he,hf⟩
  · have h := congrArg (SatNineClusterPlacement.ownsTentacles x) (he.symm.trans hf)
    rw [heown.1,hfown.2] at h
    contradiction
  · have h := congrArg (SatNineClusterPlacement.ownsTentacles x) (he.symm.trans hf)
    rw [heown.2,hfown.1] at h
    contradiction
  · exact Or.inr ⟨he,hf⟩

theorem mem_original (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) (p : Point) :
    p∈original x hw e ↔ p∈SatBipartiteDrawing.route x hw e := mem_orient _ _ _

theorem mem_subdivide (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x)
    (p : Point) (hp : p ∈route x hw e) :
    p∈LatticeSubdivision.subdivide 64 (original x hw e) :=
  LatticeRouteCore.mem_subdivide 64 2 (endCut x hw e) _ p hp

theorem original_vertex_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : Vertex x) :
    SatBipartiteDrawing.point x hw v∈original x hw e ↔ v=owner x e ∨ v=recipient x e := by
  rw [mem_original,SatBipartiteDrawing.actual_vertex_clear,incident_iff]

/-- Distinct owner-oriented original routes still have at most one common
point, since the edge catalogue has unique unordered endpoints. -/
theorem original_shared_point_unique (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p q : Point)
    (hpe : p ∈original x hw e) (hpf : p ∈original x hw f)
    (hqe : q ∈original x hw e) (hqf : q ∈original x hw f) : p=q :=
  SatBipartiteCorridors.original_shared_point_unique x hw e f hef p q
    ((mem_original x hw e p).mp hpe) ((mem_original x hw f p).mp hpf)
    ((mem_original x hw e q).mp hqe) ((mem_original x hw f q).mp hqf)

theorem original_shared_vertex (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p : Point)
    (hpe : p ∈original x hw e) (hpf : p ∈original x hw f) :
    ∃ v : Vertex x, p=SatBipartiteDrawing.point x hw v ∧
      (v=owner x e ∨ v=recipient x e) ∧ (v=owner x f ∨ v=recipient x f) := by
  obtain ⟨v,hv,hve,hvf⟩ := SatBipartiteDrawing.shared_vertex x hw e f hef p
    ((mem_original x hw e p).mp hpe) ((mem_original x hw f p).mp hpf)
  exact ⟨v,hv,(incident_iff x e v).mpr hve,(incident_iff x f v).mpr hvf⟩

/-- Any coincidence or adjacency between two width-two neighborhoods of
different dock corridors is localized within seven steps of a graph vertex
incident to both edges. This includes edges with a common owner or recipient. -/
theorem near_shared_vertex (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p q u v : Point)
    (hp : p ∈route x hw e) (hq : q ∈route x hw f)
    (hpu : IntegerGrid.manhattan p u ≤2) (hqv : IntegerGrid.manhattan q v ≤2)
    (huv : IntegerGrid.manhattan u v ≤1) :
    ∃ w : Vertex x, (w=owner x e ∨ w=recipient x e) ∧
      (w=owner x f ∨ w=recipient x f) ∧
      IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw w) u≤7 ∧
      IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw w) v≤7 := by
  obtain ⟨z,hze,hzf,hzu,hzv⟩ := LatticeRouteCore.subdivision_neighborhood_shared_vertex
    64 2 1 (original x hw e) (original x hw f)
    (original_certificate x hw e).2.1 (original_certificate x hw f).2.1
    (original_shared_point_unique x hw e f hef) p q u v
    (mem_subdivide x hw e p hp) (mem_subdivide x hw f q hq) hpu hqv huv (by decide)
  obtain ⟨w,rfl,hwe,hwf⟩ := original_shared_vertex x hw e f hef z hze hzf
  exact ⟨w,hwe,hwf,hzu,hzv⟩

/-- The recipient cut keeps every corridor point at its full chosen
endpoint radius, at least eight steps from the recipient anchor. -/
theorem recipient_anchor_clearance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (p : Point) (hp : p ∈route x hw e) :
    endCut x hw e≤IntegerGrid.manhattan
      (SatNineClusterPlacement.anchor x hw (recipient x e)) p := by
  have hc := original_certificate x hw e
  have he : (original x hw e)[(original x hw e).length-1]'(by omega)=
      SatBipartiteDrawing.point x hw (recipient x e) := by
    simpa [LatticeRouteDirections.endpointPoint,LatticeRouteDirections.orient,
      endpointVertex] using original_endpoint x hw e true
  have h := LatticeRouteCore.terminal_clearance 64 2 (endCut x hw e) (by decide)
    (by have := endCut_bounds x hw e; omega) (original x hw e) hc.1 hc.2.1 hc.2.2.1 p hp
  simpa only [he,SatNineClusterPlacement.anchor] using h

/-- Before the final collar is attached, the width-two corridor is still
three steps from every vertex of its receiving nine-cluster. -/
theorem recipient_cluster_clearance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (p q c : Point) (hp : p ∈route x hw e)
    (hpq : IntegerGrid.manhattan p q ≤2)
    (hc : c ∈SatNineClusterPlacement.points x hw (recipient x e)) :
    3≤IntegerGrid.manhattan c q := by
  have hd := recipient_anchor_clearance x hw e p hp
  have hb := (endCut_bounds x hw e).1
  have hr := SatNineClusterPlacement.radius x hw (recipient x e) c hc
  have ht1 := IntegerGrid.manhattan_triangle
    (SatNineClusterPlacement.anchor x hw (recipient x e)) c p
  have ht2 := IntegerGrid.manhattan_triangle c q p
  rw [IntegerGrid.manhattan_comm q p] at ht2
  omega

/-- The centerline witnesses in a possible contact are themselves within
five steps of the shared anchor; the strip points are within seven. -/
theorem near_shared_vertex_centers (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p q u v : Point)
    (hp : p ∈route x hw e) (hq : q ∈route x hw f)
    (hpu : IntegerGrid.manhattan p u ≤2) (hqv : IntegerGrid.manhattan q v ≤2)
    (huv : IntegerGrid.manhattan u v ≤1) :
    ∃ w : Vertex x, (w=owner x e ∨ w=recipient x e) ∧
      (w=owner x f ∨ w=recipient x f) ∧
      IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw w) p≤5 ∧
      IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw w) q≤5 ∧
      IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw w) u≤7 ∧
      IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw w) v≤7 := by
  have ht1 := IntegerGrid.manhattan_triangle p u q
  have ht2 := IntegerGrid.manhattan_triangle u v q
  rw [IntegerGrid.manhattan_comm v q] at ht2
  have hpq : IntegerGrid.manhattan p q≤5 := by omega
  obtain ⟨z,hze,hzf,hzp,hzq,_⟩ := LatticeRouteCore.subdivision_near_shared_vertex
    64 (original x hw e) (original x hw f)
    (original_certificate x hw e).2.1 (original_certificate x hw f).2.1
    (original_shared_point_unique x hw e f hef) p q
    (mem_subdivide x hw e p hp) (mem_subdivide x hw f q hq) (by omega)
  obtain ⟨w,rfl,hwe,hwf⟩ := original_shared_vertex x hw e f hef z hze hzf
  have hzu := IntegerGrid.manhattan_triangle
    (SatNineClusterPlacement.anchor x hw w) p u
  have hzv := IntegerGrid.manhattan_triangle
    (SatNineClusterPlacement.anchor x hw w) q v
  change IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw w) p≤_ at hzp
  change IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw w) q≤_ at hzq
  exact ⟨w,hwe,hwf,by omega,by omega,by omega,by omega⟩

/-- A possible contact of two width-two corridor neighborhoods can only
occur at their common owner. Recipient cuts exclude the other incidence case. -/
theorem near_shared_owner (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (p q u v : Point)
    (hp : p ∈route x hw e) (hq : q ∈route x hw f)
    (hpu : IntegerGrid.manhattan p u ≤2) (hqv : IntegerGrid.manhattan q v ≤2)
    (huv : IntegerGrid.manhattan u v ≤1) :
    owner x e=owner x f ∧
      IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw (owner x e)) u≤7 ∧
      IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw (owner x f)) v≤7 := by
  obtain ⟨w,hwe,hwf,hwp,_,hwu,hwv⟩ :=
    near_shared_vertex_centers x hw e f hef p q u v hp hq hpu hqv huv
  rcases shared_endpoint_roles x e f w hwe hwf with ⟨he,hf⟩ | ⟨he,_⟩
  · exact ⟨he.symm.trans hf,by simpa only [he] using hwu,by simpa only [hf] using hwv⟩
  · have hr := recipient_anchor_clearance x hw e p hp
    have hb := (endCut_bounds x hw e).1
    rw [he] at hwp
    omega

/-- Distinct edges with the same owner use different concrete dock sides. -/
theorem owner_sides_ne (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (ho : owner x e =owner x f) :
    side x hw e false≠side x hw f false := by
  intro he
  have hd := NineClusterDockGeometry.sideOfDirection_injective he
  have hn := SatBipartiteDirections.direction_ne x hw e f hef
    (reverseEdge x e) (reverseEdge x f) ho
  exact hn hd

/-- The graph coloring globally separates all owner vertices from all
recipient vertices, including endpoints of different edges. -/
theorem owner_recipient_ne (x : SatTy.denote) (e f : Edge x) : owner x e≠recipient x f := by
  intro he
  have h := congrArg (SatNineClusterPlacement.ownsTentacles x) he
  rw [(SatCollarCorridors.owners x e).1,(SatCollarCorridors.owners x f).2] at h
  contradiction

/-- Distinct edges meeting the same receiving cluster use different
receiving sides as well as different owner sides. -/
theorem recipient_sides_ne (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (hr : recipient x e =recipient x f) :
    side x hw e true≠side x hw f true := by
  intro he
  have hd := NineClusterDockGeometry.sideOfDirection_injective he
  have hn := SatBipartiteDirections.direction_ne x hw e f hef
    (!(reverseEdge x e)) (!(reverseEdge x f)) hr
  exact hn hd

/-- Every vertex unrelated to an edge remains sixty-four steps from its
entire asymmetric corridor, independent of the chosen endpoint cuts. -/
theorem unrelated_anchor_clearance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : Vertex x) (hvo : v ≠owner x e) (hvr : v ≠recipient x e)
    (p : Point) (hp : p ∈route x hw e) :
    64≤IntegerGrid.manhattan (SatNineClusterPlacement.anchor x hw v) p := by
  have hn : SatBipartiteDrawing.point x hw v∉original x hw e := by
    rw [original_vertex_iff]
    exact not_or.mpr ⟨hvo,hvr⟩
  have h := LatticeRouteCore.unrelated_clearance 64 2 (endCut x hw e) (original x hw e)
    (original_certificate x hw e).2.1 (SatBipartiteDrawing.point x hw v) hn p hp
  simpa only [SatNineClusterPlacement.anchor,IntegerGrid.manhattan_comm] using h

/-- Thickening by two units leaves a sixty-two-step margin from unrelated
cluster anchors, and hence a fifty-nine-step margin from their nine-clusters. -/
theorem unrelated_cluster_clearance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : Vertex x) (hvo : v ≠owner x e) (hvr : v ≠recipient x e)
    (p q c : Point) (hp : p ∈route x hw e) (hpq : IntegerGrid.manhattan p q ≤2)
    (hc : c ∈SatNineClusterPlacement.points x hw v) :
    59≤IntegerGrid.manhattan c q := by
  have hd := unrelated_anchor_clearance x hw e v hvo hvr p hp
  have hr := SatNineClusterPlacement.radius x hw v c hc
  have ht1 := IntegerGrid.manhattan_triangle (SatNineClusterPlacement.anchor x hw v) c p
  have ht2 := IntegerGrid.manhattan_triangle c q p
  rw [IntegerGrid.manhattan_comm q p] at ht2
  omega

end GridHardness.SatDockCorridors
