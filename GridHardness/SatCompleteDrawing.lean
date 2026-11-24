/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatDrawingSelectionCode
public import GridHardness.SatWireDrawingDirections

/-!
# SAT Complete Drawing

A complete orthogonal drawing indexed by actual arcs of the final SAT
graph. The SAT-fed catalogue is searched by its ordered endpoint key. A
proof-only catalogue index witnesses that executable selection, so all the
simultaneous geometric certificates apply to exactly the computed path.
-/

@[expose] public section

namespace GridHardness.SatCompleteDrawing
open CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Vertex := SatRouteCatalogue.Vertex
abbrev Point := Int × Int

/-- Actual directed arcs, carrying their adjacency proof. -/
abbrev Arc (x : SatTy.denote) :=
  {uv : Vertex x × Vertex x // (SatClauseOrder.graph (finiteFormula x)).adj uv.1 uv.2}

def source (x : SatTy.denote) (a : Arc x) : Vertex x := a.val.1
def target (x : SatTy.denote) (a : Arc x) : Vertex x := a.val.2

noncomputable def point (x : SatTy.denote) : Vertex x → Point :=
  SatGlobalVertexPlacement.actualPoint (finiteFormula x)

/-- A catalogue witness for the computably selected route. -/
noncomputable def index (x : SatTy.denote) (a : Arc x) : SatWireDrawingGeometry.Edge x :=
  Classical.choose (SatDrawingSelectionCode.selected_exists x a.val.1 a.val.2 a.property)

theorem index_source (x : SatTy.denote) (a : Arc x) :
    SatWireDrawingGeometry.source x (index x a)=source x a :=
  (Classical.choose_spec (SatDrawingSelectionCode.selected_exists x a.val.1 a.val.2 a.property)).1

theorem index_target (x : SatTy.denote) (a : Arc x) :
    SatWireDrawingGeometry.target x (index x a)=target x a :=
  (Classical.choose_spec (SatDrawingSelectionCode.selected_exists x a.val.1 a.val.2 a.property)).2.1

/-- Distinct actual arcs always receive distinct catalogue indices.
This does not require every catalogue index to be uniquely determined by
its endpoints. -/
theorem index_injective (x : SatTy.denote) : Function.Injective (index x) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · change source x a=source x b
    rw [← index_source,← index_source,h]
  · change target x a=target x b
    rw [← index_target,← index_target,h]

noncomputable def route (x : SatTy.denote) (a : Arc x) : List Point :=
  SatWireDrawingGeometry.route x (index x a)

/-- The observable path is exactly the endpoint-key lookup program's output. -/
theorem route_encoded (x : SatTy.denote) (a : Arc x) :
    (route x a).map GridProblems.GridCode.encodePoint=
      SatDrawingSelectionCode.lookup.eval (x,
        (SatDrawingSelectionCode.label x (source x a),SatDrawingSelectionCode.label x (target x a))) :=
  (Classical.choose_spec (SatDrawingSelectionCode.selected_exists x a.val.1 a.val.2 a.property)).2.2

noncomputable def Incident (x : SatTy.denote) (a : Arc x) (q : Point) : Prop :=
  q=point x (source x a) ∨ q=point x (target x a)

theorem point_injective (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) :
    Function.Injective (point x) :=
  SatGlobalVertexPlacement.actualPoint_injective (finiteFormula x)
    (SatVariablePlacement.finite_regular x hw)

/-- Every actual arc is assigned a simple unit-step path with the right
endpoints and a linear length bound. -/
theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (a : Arc x) :
    (route x a).head?=some (point x (source x a)) ∧
    (route x a).getLast?=some (point x (target x a)) ∧
    (route x a).Nodup ∧ (route x a).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2≤(route x a).length ∧ (route x a).length≤6144*(x.length+1) := by
  simpa only [route,point,index_source,index_target] using
    SatWireDrawingGeometry.route_certificate x hw (index x a)

theorem route_length_lower (x : SatTy.denote) (a : Arc x) :
    3≤(route x a).length :=
  SatWireDrawingGeometry.route_length_lower x (index x a)

theorem route_bounds (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (q : Point) (hq : q ∈route x a) :
    -128≤q.1 ∧ q.1≤SatVariableLattice.wireX (3*x.length)+128 ∧
      -64≤q.2 ∧ q.2≤SatExteriorLattice.top (3*x.length) :=
  SatWireDrawingGeometry.route_bounds x hw (index x a) q hq

/-- An actual vertex lies on an arc's path exactly when it is an endpoint. -/
theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (v : Vertex x) :
    point x v∈route x a ↔ v=source x a ∨ v=target x a := by
  simpa only [route,point,index_source,index_target] using
    SatWireDrawingGeometry.actual_vertex_clear x hw (index x a) v

/-- All distinct actual arcs meet only at endpoints of both arcs. -/
theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a b : Arc x) (hab : a ≠b) (q : Point) (ha : q ∈route x a) (hb : q ∈route x b) :
    Incident x a q ∧ Incident x b q := by
  simpa only [Incident,point,SatWireDrawingGeometry.Incident,index_source,index_target] using
    SatWireDrawingGeometry.route_intersection x hw (index x a) (index x b)
      (fun h => hab (index_injective x h)) q ha hb

/-- An intersection identifies a single actual graph vertex shared by
both directed arcs. -/
theorem shared_vertex (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a b : Arc x) (hab : a ≠b) (q : Point) (ha : q ∈route x a) (hb : q ∈route x b) :
    ∃ v : Vertex x, q=point x v ∧
      (v=source x a ∨ v=target x a) ∧ (v=source x b ∨ v=target x b) := by
  simpa only [point,index_source,index_target] using
    SatWireDrawingGeometry.shared_vertex x hw (index x a) (index x b)
      (fun h => hab (index_injective x h)) q ha hb

/-- `false` denotes the source; `true` denotes the target. -/
def endpointVertex (x : SatTy.denote) (a : Arc x) (atEnd : Bool) : Vertex x :=
  if atEnd then target x a else source x a

noncomputable def direction (x : SatTy.denote) (a : Arc x) (atEnd : Bool) : Fin 4 :=
  SatWireDrawingDirections.direction x (index x a) atEnd

theorem index_endpoint (x : SatTy.denote) (a : Arc x) (b : Bool) :
    SatWireDrawingDirections.endpointVertex x (index x a) b=endpointVertex x a b := by
  cases b <;> simp [SatWireDrawingDirections.endpointVertex,endpointVertex,index_source,index_target]

/-- The first step at either endpoint uses the selected cardinal port. -/
theorem direction_spec (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a : Arc x) (b : Bool) :
    LatticeRouteDirections.neighborPoint (route x a) b
      (by have := route_length_lower x a; omega)=
        LatticeRouteDirections.step (point x (endpointVertex x a b)) (direction x a b) := by
  simpa only [route,point,direction,index_endpoint] using
    SatWireDrawingDirections.direction_spec x hw (index x a) b

theorem direction_ne (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (a b : Arc x) (hab : a ≠b) (r s : Bool)
    (hv : endpointVertex x a r =endpointVertex x b s) :
    direction x a r≠direction x b s := by
  apply SatWireDrawingDirections.direction_ne x hw (index x a) (index x b)
    (fun h => hab (index_injective x h)) r s
  simpa only [index_endpoint] using hv

theorem endpoints_ne (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (a : Arc x) :
    source x a≠target x a := by
  simpa only [index_source,index_target] using
    SatWireDrawingGeometry.endpoints_ne x hw (index x a)

abbrev Incidence (x : SatTy.denote) (v : Vertex x) :=
  {i : Arc x × Bool // endpointVertex x i.1 i.2=v}

/-- The actual graph incidences, including both orientations, occupy
pairwise distinct cardinal ports at every vertex. -/
theorem incident_directions_injective (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) :
    Function.Injective (fun i : Incidence x v => direction x i.val.1 i.val.2) := by
  rintro ⟨⟨a,r⟩,ha⟩ ⟨⟨b,s⟩,hb⟩ h
  dsimp at ha hb h
  apply Subtype.ext
  by_cases hab : a=b
  · subst b
    have hrs : r=s := by
      cases r <;> cases s
      · rfl
      · exact False.elim (endpoints_ne x hw a (ha.trans hb.symm))
      · exact False.elim (endpoints_ne x hw a (hb.trans ha.symm))
      · rfl
    exact Prod.ext rfl hrs
  · exact False.elim (direction_ne x hw a b hab r s (ha.trans hb.symm) h)

end GridHardness.SatCompleteDrawing
