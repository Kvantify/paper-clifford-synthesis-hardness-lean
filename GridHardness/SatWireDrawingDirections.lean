/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.LatticeRouteDirections
public import GridHardness.SatWireDrawingGeometry

/-!
# SAT Wire Drawing Directions

Distinct cardinal directions for every incidence of the combined
candidate-route drawing, including the vertical and residual lanes. These
are geometric port certificates in the actual vertex placement. They do
not assert adjacency or exhaustiveness for the candidate endpoint pairs.
-/

@[expose] public section

namespace GridHardness.SatWireDrawingDirections
open CliffordSynthesis CliffordComplexity PlanarSatAssembly SatWireDrawingGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Vertex (x : SatTy.denote) := (SatClauseOrder.graph (finiteFormula x)).Vertex

/-- `false` selects the source; `true` selects the target. -/
noncomputable def endpointVertex (x : SatTy.denote) (e : Edge x) (atEnd : Bool) : Vertex x :=
  if atEnd then target x e else source x e

def direction (x : SatTy.denote) (e : Edge x) (atEnd : Bool) : Fin 4 :=
  LatticeRouteDirections.tangent (route x e) atEnd
    (by have := route_length_lower x e; omega)

theorem endpointPoint_eq (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) :
    LatticeRouteDirections.endpointPoint (route x e) b
      (by have := route_length_lower x e; omega)=
        SatGlobalVertexPlacement.actualPoint (finiteFormula x) (endpointVertex x e b) := by
  have hs := LatticeRouteDirections.endpointPoint_spec (route x e) b
    (by have := route_length_lower x e; omega)
  have hc := route_certificate x hw e
  cases b
  · exact Option.some.inj (hs.symm.trans hc.1)
  · exact Option.some.inj (hs.symm.trans hc.2.1)

theorem endpoint_iff (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (q : Int × Int) :
    LatticeRouteDirections.Endpoint (route x e) q ↔ Incident x e q := by
  have hc := route_certificate x hw e
  simp only [LatticeRouteDirections.Endpoint,hc.1,hc.2.1,Option.some.injEq,
    Incident,eq_comm]

/-- The neighboring lattice point lies on the ray based at the actual
source or target vertex of the final graph. -/
theorem direction_spec (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) :
    LatticeRouteDirections.neighborPoint (route x e) b
      (by have := route_length_lower x e; omega)=
        LatticeRouteDirections.step
          (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (endpointVertex x e b))
          (direction x e b) := by
  have hc := route_certificate x hw e
  have hs := LatticeRouteDirections.tangent_spec (route x e) b hc.2.2.2.2.1 hc.2.2.2.1
  simpa only [endpointPoint_eq x hw e b,direction] using hs

theorem neighbor_ne_vertex (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (b : Bool) (v : Vertex x) :
    LatticeRouteDirections.neighborPoint (route x e) b
      (by have := route_length_lower x e; omega)≠
        SatGlobalVertexPlacement.actualPoint (finiteFormula x) v := by
  apply LatticeRouteDirections.neighborPoint_ne_vertex _ (route x e) b
    (by have := route_length_lower x e; omega) (route_certificate x hw e).2.2.1
  intro w hw'
  apply (endpoint_iff x hw e _).mpr
  exact incident_of_vertex_mem x hw e _ w rfl hw'

theorem direction_ne (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hef : e ≠f) (b c : Bool)
    (hv : endpointVertex x e b =endpointVertex x f c) :
    direction x e b≠direction x f c := by
  have hl := route_certificate x hw e
  have hm := route_certificate x hw f
  apply LatticeRouteDirections.tangent_ne (route x e) (route x f) b c
    (by have := route_length_lower x e; omega)
    (by have := route_length_lower x f; omega) hl.2.2.1 hl.2.2.2.1 hm.2.2.2.1
  · rw [endpointPoint_eq x hw e b,endpointPoint_eq x hw f c,hv]
  · intro q he hf
    have hi := route_intersection x hw e f hef q he hf
    exact ⟨(endpoint_iff x hw e q).mpr hi.1,(endpoint_iff x hw f q).mpr hi.2⟩

abbrev Incidence (x : SatTy.denote) (v : Vertex x) :=
  {i : Edge x × Bool // endpointVertex x i.1 i.2=v}

/-- Every indexed candidate-route incidence at a vertex has a distinct
cardinal direction, regardless of its chosen orientation. -/
theorem incident_directions_injective (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (v : Vertex x) :
    Function.Injective (fun i : Incidence x v => direction x i.val.1 i.val.2) := by
  rintro ⟨⟨e,b⟩,hi⟩ ⟨⟨f,c⟩,hj⟩ he
  dsimp at hi hj he
  apply Subtype.ext
  by_cases hef : e=f
  · subst f
    have hbc : b=c := by
      cases b <;> cases c
      · rfl
      · exact False.elim (endpoints_ne x hw e (hi.trans hj.symm))
      · exact False.elim (endpoints_ne x hw e (hj.trans hi.symm))
      · rfl
    exact Prod.ext rfl hbc
  · exact False.elim (direction_ne x hw e f hef b c (hi.trans hj.symm) he)

end GridHardness.SatWireDrawingDirections
