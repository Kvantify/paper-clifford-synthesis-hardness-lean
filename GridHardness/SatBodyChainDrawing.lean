/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatExteriorBodyIntersection
public import GridHardness.SatVariableChainClearance

/-!
# SAT Body Chain Drawing

One simultaneous route family for the variable/clause bodies,
variable occurrence chains, and exterior backbone. Every indexed edge is
an actual final-graph arc. Clause-to-wire links and internal wire arcs are
not in this family, so no complete graph drawing is asserted here.
-/

@[expose] public section

namespace GridHardness.SatBodyChainDrawing
open CliffordSynthesis CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Edge (x : SatTy.denote) :=
  SatBodyDrawing.Edge ((vsOf x).length+1) x.length ⊕
    (SatVariableChainDrawing.Edge (finiteFormula x) ⊕ SatExteriorDrawing.Edge x.length)

noncomputable def source (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatBodyDrawing.source (finiteFormula x) e
  | .inr (.inl e) => SatVariableChainDrawing.vertex (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) (SatVariableChainDrawing.endpoints e).1
  | .inr (.inr e) => SatExteriorDrawing.sourceVertex x e

noncomputable def target (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatBodyDrawing.target (finiteFormula x) e
  | .inr (.inl e) => SatVariableChainDrawing.vertex (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) (SatVariableChainDrawing.endpoints e).2
  | .inr (.inr e) => SatExteriorDrawing.targetVertex x e

def route (x : SatTy.denote) : Edge x → List (Int × Int)
  | .inl e => SatBodyDrawing.route (finiteFormula x) e
  | .inr (.inl e) => SatVariableChainDrawing.route e
  | .inr (.inr e) => SatExteriorDrawing.route x e

noncomputable def Incident (x : SatTy.denote) (e : Edge x) (q : Int × Int) : Prop :=
  q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e) ∨
    q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)

theorem edge_is_arc (x : SatTy.denote) (e : Edge x) :
    (SatClauseOrder.graph (finiteFormula x)).adj (source x e) (target x e) := by
  rcases e with e | e | e
  · exact SatBodyDrawing.edge_is_arc _ e
  · exact SatVariableChainDrawing.edge_is_arc _ _ e
  · exact SatExteriorDrawing.edge_is_arc x e

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) (e : Edge x) :
    (route x e).head?=some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e)) ∧
    (route x e).getLast?=some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)) ∧
    (route x e).Nodup ∧ (route x e).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2≤(route x e).length ∧ (route x e).length≤4096*(x.length+1) := by
  rcases e with e | e | e
  · obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatBodyDrawing.route_certificate (finiteFormula x)
      (SatVariablePlacement.finite_regular x hw) e
    exact ⟨hh,ht,hn,hc,hl,by change (SatBodyDrawing.route (finiteFormula x) e).length≤_; omega⟩
  · have he := SatVariableChainDrawing.actual_route_endpoints (finiteFormula x) e
    have hs := SatVariableChainDrawing.route_simple e
    have hl := SatVariableChainDrawing.route_length e
    exact ⟨he.1,he.2,hs.1,hs.2,hl.1,by change (SatVariableChainDrawing.route e).length≤_; omega⟩
  · have he := SatExteriorDrawing.route_endpoints x hw e
    have hs := SatExteriorDrawing.route_simple x e
    have hl := SatExteriorDrawing.route_length_bound x e
    exact ⟨he.1,he.2,hs.1,hs.2,hl⟩

theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (v : (SatClauseOrder.graph (finiteFormula x)).Vertex) :
    SatGlobalVertexPlacement.actualPoint (finiteFormula x) v∈route x e ↔
      v=source x e ∨ v=target x e := by
  rcases e with e | e | e
  · exact SatBodyDrawing.actual_vertex_clear _ (SatVariablePlacement.finite_regular x hw) e v
  · exact SatVariableChainClearance.finite_global_vertex_clear x hw e v
  · exact SatExteriorDrawing.actual_vertex_clear x hw e v

theorem route_bounds (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x) (q : Int × Int) (hq : q ∈route x e) :
    -128≤q.1 ∧ q.1≤SatVariableLattice.wireX (3*x.length)+128 ∧
      -64≤q.2 ∧ q.2≤SatExteriorLattice.top (3*x.length) := by
  rcases e with e | e | e
  · have h := SatBodyDrawing.route_bounds (finiteFormula x)
      (SatVariablePlacement.finite_regular x hw) e q hq
    dsimp [SatExteriorLattice.top]
    omega
  · have h := SatVariableChainDrawing.route_bounds e q hq
    dsimp [SatVariableLattice.wireX,SatExteriorLattice.top] at h ⊢
    omega
  · exact SatExteriorDrawing.route_bounds x e q hq

theorem chain_body_intersection (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : SatVariableChainDrawing.Edge (finiteFormula x))
    (f : SatBodyDrawing.Edge ((vsOf x).length +1) x.length) (q : Int × Int)
    (he : q ∈SatVariableChainDrawing.route e) (hf : q ∈SatBodyDrawing.route (finiteFormula x) f) :
    Incident x (.inr (.inl e)) q ∧ Incident x (.inl f) q := by
  cases f with
  | inl f =>
    have h := SatVariableChainSeparation.body_route_intersection (finiteFormula x)
      (SatVariablePlacement.finite_regular x hw) (SatClauseOrder.permutation (finiteFormula x))
      e f q he hf
    simpa only [Incident,source,target,SatVariableChainDrawing.actualPoint_vertex,
      SatBodyDrawing.source_point,SatBodyDrawing.target_point,SatBodyDrawing.endpoints,
      SatGlobalVertexPlacement.bodyPoint,SatVariablePlacement.vertexPoint] using h
  | inr f =>
    have h := SatVariableChainClearance.clause_route_separation e f q q he hf
    simp [IntegerGrid.manhattan] at h

theorem chain_exterior_intersection (x : SatTy.denote)
    (e : SatVariableChainDrawing.Edge (finiteFormula x))
    (f : SatExteriorDrawing.Edge x.length) (q : Int × Int)
    (he : q ∈SatVariableChainDrawing.route e) (hf : q ∈SatExteriorDrawing.route x f) :
    Incident x (.inr (.inl e)) q ∧ Incident x (.inr (.inr f)) q := by
  obtain ⟨_,hc,hf⟩ := SatVariableChainClearance.exterior_intersection x e f q he hf
  refine ⟨Or.inl ?_,Or.inr hf⟩
  simpa only [source,SatVariableChainDrawing.actualPoint_vertex] using hc

/-- The three assembled families have no intersection in either
route's interior. This includes every mixed-family pair. -/
theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e f : Edge x) (hne : e ≠f) (q : Int × Int) (he : q ∈route x e) (hf : q ∈route x f) :
    Incident x e q ∧ Incident x f q := by
  rcases e with e | e | e
  · rcases f with f | f | f
    · exact SatBodyDrawing.route_intersection _ (SatVariablePlacement.finite_regular x hw)
        e f (fun h => hne (congrArg Sum.inl h)) q he hf
    · exact (chain_body_intersection x hw f e q hf he).symm
    · exact (SatExteriorDrawing.body_route_intersection x hw f e q hf he).symm
  · rcases f with f | f | f
    · exact chain_body_intersection x hw e f q he hf
    · exact False.elim (List.disjoint_left.mp
        (SatVariableChainSeparation.routes_disjoint e f
          (fun h => hne (congrArg Sum.inr (congrArg Sum.inl h)))) he hf)
    · exact chain_exterior_intersection x e f q he hf
  · rcases f with f | f | f
    · exact SatExteriorDrawing.body_route_intersection x hw e f q he hf
    · exact (chain_exterior_intersection x f e q hf he).symm
    · exact SatExteriorDrawing.actual_route_intersection x e f
        (fun h => hne (congrArg Sum.inr (congrArg Sum.inr h))) q he hf

end GridHardness.SatBodyChainDrawing
