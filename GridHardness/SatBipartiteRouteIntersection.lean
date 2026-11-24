/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartiteRoutes
public import GridHardness.SatScaledIntersection
public import GridHardness.LatticeRouteTrimIntersection

/-!
# SAT Bipartite Route Intersection

Intersections and bounds for the external paths of the bipartite
replacement. Trimming the scaled directed routes moves their endpoints
onto gadget ports while preserving endpoint-only intersections.
-/

@[expose] public section

namespace GridHardness.SatBipartiteRoutes
open CliffordComplexity CliffordSynthesis LatticeSubdivision
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable def Incident (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (q : Point) : Prop :=
  q=SatBipartitePlacement.point x hw (SatCompleteDrawing.source x a,3) ∨
  q=SatBipartitePlacement.point x hw (SatCompleteDrawing.target x a,0)

theorem endpoint_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (q : Point) :
    LatticeRouteDirections.Endpoint (route x hw a) q ↔ Incident x hw a q := by
  obtain ⟨hh,ht,_⟩ := route_certificate x hw a
  simp [LatticeRouteDirections.Endpoint,hh,ht,Incident,eq_comm]

/-- External paths of distinct arcs intersect only at their new gadget ports. -/
theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a b : Arc x) (hab : a ≠b) (q : Point)
    (ha : q ∈route x hw a) (hb : q ∈route x hw b) :
    Incident x hw a q ∧ Incident x hw b q := by
  have hinter : ∀ z, z∈SatScaledDrawing.route x a → z∈SatScaledDrawing.route x b →
      LatticeRouteDirections.Endpoint (SatScaledDrawing.route x a) z ∧
      LatticeRouteDirections.Endpoint (SatScaledDrawing.route x b) z := by
    intro z hza hzb
    obtain ⟨hea,heb⟩ := SatScaledDrawing.route_intersection x hw a b hab z hza hzb
    exact ⟨(SatScaledDrawing.endpoint_iff x hw a z).mpr hea,
      (SatScaledDrawing.endpoint_iff x hw b z).mpr heb⟩
  obtain ⟨hea,heb⟩ := LatticeRouteTrim.endpoint_intersection
    (radius x hw a false) (radius x hw a true)
    (radius x hw b false) (radius x hw b true)
    (SatScaledDrawing.route x a) (SatScaledDrawing.route x b)
    (SatScaledDrawing.route_certificate x hw a).2.2.1
    (SatScaledDrawing.route_certificate x hw b).2.2.1 hinter q ha hb
  exact ⟨(endpoint_iff x hw a q).mp hea,(endpoint_iff x hw b q).mp heb⟩

/-- An intersection represents one actual vertex of the bipartite graph,
shared as an attachment port by both external paths. -/
theorem shared_vertex (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a b : Arc x) (hab : a ≠b) (q : Point)
    (ha : q ∈route x hw a) (hb : q ∈route x hw b) :
    ∃ v : SatBipartitePlacement.Vertex x, q=SatBipartitePlacement.point x hw v ∧
      (v=(SatCompleteDrawing.source x a,3) ∨ v=(SatCompleteDrawing.target x a,0)) ∧
      (v=(SatCompleteDrawing.source x b,3) ∨ v=(SatCompleteDrawing.target x b,0)) := by
  obtain ⟨hea,heb⟩ := route_intersection x hw a b hab q ha hb
  have hclass (v : SatBipartitePlacement.Vertex x)
      (hv : q=SatBipartitePlacement.point x hw v) :
      v=(SatCompleteDrawing.source x b,3) ∨ v=(SatCompleteDrawing.target x b,0) := by
    rcases heb with heb | heb
    · exact Or.inl (SatBipartitePlacement.point_injective x hw (hv.symm.trans heb))
    · exact Or.inr (SatBipartitePlacement.point_injective x hw (hv.symm.trans heb))
  rcases hea with hea | hea
  · exact ⟨(SatCompleteDrawing.source x a,3),hea,Or.inl rfl,hclass _ hea⟩
  · exact ⟨(SatCompleteDrawing.target x a,0),hea,Or.inr rfl,hclass _ hea⟩

/-- Removing the short endpoint portions does not enlarge the scaled
rectangular coordinate bounds. -/
theorem route_bounds (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (q : Point) (hq : q ∈route x hw a) :
    -2048≤q.1 ∧ q.1≤16*(SatVariableLattice.wireX (3*x.length)+128) ∧
      -1024≤q.2 ∧ q.2≤16*SatExteriorLattice.top (3*x.length) :=
  SatScaledDrawing.route_bounds x hw a q (mem_scaled x hw a q hq)

/-- External paths whose original arcs have no common endpoint keep the
full sixteen-step separation of the scaled directed drawing. -/
theorem nonincident_distance (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a b : Arc x)
    (hss : SatCompleteDrawing.source x a ≠SatCompleteDrawing.source x b)
    (hst : SatCompleteDrawing.source x a ≠SatCompleteDrawing.target x b)
    (hts : SatCompleteDrawing.target x a ≠SatCompleteDrawing.source x b)
    (htt : SatCompleteDrawing.target x a ≠SatCompleteDrawing.target x b)
    (p q : Point) (hp : p ∈route x hw a) (hq : q ∈route x hw b) :
    16≤IntegerGrid.manhattan p q :=
  SatScaledDrawing.nonincident_distance x hw a b hss hst hts htt p q
    (mem_scaled x hw a p hp) (mem_scaled x hw b q hq)

end GridHardness.SatBipartiteRoutes
