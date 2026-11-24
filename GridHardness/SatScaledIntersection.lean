/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatScaledDrawing
public import GridHardness.LatticeRouteIntersection

/-!
# SAT Scaled Intersection

Simultaneous separation of all dilated SAT routes. Distinct arcs retain
endpoint-only intersections; arcs without a common graph vertex have a
sixteen-step separation. The rectangular coordinate bounds also scale by
sixteen.
-/

@[expose] public section

namespace GridHardness.SatScaledDrawing
open CliffordComplexity PlanarSatAssembly CliffordSynthesis LatticeSubdivision
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable def Incident (x : SatTy.denote) (a : Arc x) (q : Point) : Prop :=
  q=point x (SatCompleteDrawing.source x a) ∨ q=point x (SatCompleteDrawing.target x a)

theorem point_injective (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    Function.Injective (point x) := by
  intro u v he
  apply SatCompleteDrawing.point_injective x hw
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp [point,scale] at hx hy
  apply Prod.ext <;> omega

theorem endpoint_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (q : Point) :
    LatticeRouteDirections.Endpoint (route x a) q ↔ Incident x a q := by
  obtain ⟨hh,ht,_⟩ := route_certificate x hw a
  simp [LatticeRouteDirections.Endpoint,hh,ht,Incident,eq_comm]

private theorem original_endpoint_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (q : Point) :
    LatticeRouteDirections.Endpoint (SatCompleteDrawing.route x a) q ↔
      SatCompleteDrawing.Incident x a q := by
  obtain ⟨hh,ht,_⟩ := SatCompleteDrawing.route_certificate x hw a
  simp [LatticeRouteDirections.Endpoint,hh,ht,SatCompleteDrawing.Incident,eq_comm]

/-- Every intersection is the scaled image of one actual graph vertex
shared by both arcs. -/
theorem shared_vertex (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a b : Arc x) (hab : a ≠b) (q : Point) (ha : q ∈route x a) (hb : q ∈route x b) :
    ∃ v : Vertex x, q=point x v ∧
      (v=SatCompleteDrawing.source x a ∨ v=SatCompleteDrawing.target x a) ∧
      (v=SatCompleteDrawing.source x b ∨ v=SatCompleteDrawing.target x b) := by
  have hca := SatCompleteDrawing.route_certificate x hw a
  have hcb := SatCompleteDrawing.route_certificate x hw b
  have hinter : ∀ z, z∈SatCompleteDrawing.route x a → z∈SatCompleteDrawing.route x b →
      LatticeRouteDirections.Endpoint (SatCompleteDrawing.route x a) z ∧
      LatticeRouteDirections.Endpoint (SatCompleteDrawing.route x b) z := by
    intro z hza hzb
    obtain ⟨hea,heb⟩ := SatCompleteDrawing.route_intersection x hw a b hab z hza hzb
    exact ⟨(original_endpoint_iff x hw a z).mpr hea,
      (original_endpoint_iff x hw b z).mpr heb⟩
  obtain ⟨z,hza,hzb,hq⟩ := subdivide_intersection 16 (by decide)
    (SatCompleteDrawing.route x a) (SatCompleteDrawing.route x b)
    (SatCompleteDrawing.route_length_lower x a) hca.2.2.1 hca.2.2.2.1 hcb.2.2.2.1
    hinter q ha hb
  have endpoint_mem (l : List Point) (z : Point) (hz : LatticeRouteDirections.Endpoint l z) :
      z∈l := by
    rcases hz with hz | hz
    · exact List.mem_of_mem_head? (by rw [hz]; simp)
    · exact List.mem_of_mem_getLast? (by rw [hz]; simp)
  obtain ⟨v,hv,hva,hvb⟩ := SatCompleteDrawing.shared_vertex x hw a b hab z
    (endpoint_mem _ z hza) (endpoint_mem _ z hzb)
  exact ⟨v,hq.trans (congrArg (scale 16) hv),hva,hvb⟩

/-- Distinct scaled routes intersect only at endpoints of both routes. -/
theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a b : Arc x) (hab : a ≠b) (q : Point) (ha : q ∈route x a) (hb : q ∈route x b) :
    Incident x a q ∧ Incident x b q := by
  obtain ⟨v,hq,hva,hvb⟩ := shared_vertex x hw a b hab q ha hb
  constructor
  · exact hva.elim (fun h => Or.inl (hq.trans (congrArg (point x) h)))
      (fun h => Or.inr (hq.trans (congrArg (point x) h)))
  · exact hvb.elim (fun h => Or.inl (hq.trans (congrArg (point x) h)))
      (fun h => Or.inr (hq.trans (congrArg (point x) h)))

/-- Routes of arcs with no common endpoint have a full sixteen-unit
margin, including every newly inserted subdivision point. -/
theorem nonincident_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a b : Arc x)
    (hss : SatCompleteDrawing.source x a ≠SatCompleteDrawing.source x b)
    (hst : SatCompleteDrawing.source x a ≠SatCompleteDrawing.target x b)
    (hts : SatCompleteDrawing.target x a ≠SatCompleteDrawing.source x b)
    (htt : SatCompleteDrawing.target x a ≠SatCompleteDrawing.target x b)
    (p q : Point) (hp : p ∈route x a) (hq : q ∈route x b) :
    16≤IntegerGrid.manhattan p q := by
  have hab : a≠b := fun he => hss (congrArg (SatCompleteDrawing.source x) he)
  have hd : List.Disjoint (SatCompleteDrawing.route x a) (SatCompleteDrawing.route x b) := by
    intro z hza hzb
    obtain ⟨v,_,hva,hvb⟩ := SatCompleteDrawing.shared_vertex x hw a b hab z hza hzb
    rcases hva with rfl | rfl
    · exact hvb.elim hss hst
    · exact hvb.elim hts htt
  exact subdivide_disjoint_clearance 16 _ _
    (SatCompleteDrawing.route_certificate x hw a).2.2.2.1
    (SatCompleteDrawing.route_certificate x hw b).2.2.2.1 hd p q hp hq

/-- Dilation keeps the entire route family inside a linear-size
rectangular coordinate range. -/
theorem route_bounds (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (q : Point) (hq : q ∈route x a) :
    -2048≤q.1 ∧ q.1≤16*(SatVariableLattice.wireX (3*x.length)+128) ∧
      -1024≤q.2 ∧ q.2≤16*SatExteriorLattice.top (3*x.length) := by
  rcases (subdivide_mem 16 (SatCompleteDrawing.route x a) q).mp hq with
      ⟨u,hu,rfl⟩ | ⟨u,v,huv,k,hk,rfl⟩
  · have hb := SatCompleteDrawing.route_bounds x hw a u (List.mem_of_getLast? hu)
    dsimp [scale]
    omega
  · have hmem := edges_mem_vertices (SatCompleteDrawing.route x a) u v huv
    have hbu := SatCompleteDrawing.route_bounds x hw a u hmem.1
    have hbv := SatCompleteDrawing.route_bounds x hw a v hmem.2
    have hbounds := interpolate_bounds 16 u v (Nat.le_of_lt hk)
    have hxmin := le_min hbu.1 hbv.1
    have hxmax := max_le hbu.2.1 hbv.2.1
    have hymin := le_min hbu.2.2.1 hbv.2.2.1
    have hymax := max_le hbu.2.2.2 hbv.2.2.2
    norm_num only at hbounds
    omega

end GridHardness.SatScaledDrawing
