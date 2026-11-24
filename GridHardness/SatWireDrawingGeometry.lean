/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVerticalCompatibility
public import GridHardness.SatResidualCompatibility

/-!
# SAT Wire Drawing Geometry

A simultaneous geometric drawing of the SAT arc families
and the vertical and residual candidate endpoint pairs. Every route is
simple, has linear coordinate and length bounds, and avoids all unrelated
vertices. Distinct routes meet only at common endpoints. No assertion is
made here that every candidate is an actual arc, or that the catalogue
exhausts all arcs of the final SAT graph.
-/

@[expose] public section

namespace GridHardness.SatWireDrawingGeometry
open CliffordSynthesis CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev VerticalEdge (x : SatTy.denote) :=
  SatVerticalDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))
abbrev ResidualEdge (x : SatTy.denote) :=
  SatResidualDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))
abbrev Edge (x : SatTy.denote) :=
  (SatLastLinkAssembly.Edge x ⊕ VerticalEdge x) ⊕ ResidualEdge x

noncomputable def source (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl (.inl e) => SatLastLinkAssembly.source x e
  | .inl (.inr e) => SatVerticalDrawing.source (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e
  | .inr e => SatResidualDrawing.source (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e

noncomputable def target (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl (.inl e) => SatLastLinkAssembly.target x e
  | .inl (.inr e) => SatVerticalDrawing.target (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e
  | .inr e => SatResidualDrawing.target (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e

def route (x : SatTy.denote) : Edge x → List Point
  | .inl (.inl e) => SatLastLinkAssembly.route x e
  | .inl (.inr e) => SatVerticalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e
  | .inr e => SatResidualDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e

noncomputable def Incident (x : SatTy.denote) (e : Edge x) (q : Point) : Prop :=
  q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e) ∨
    q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) :
    (route x e).head? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e)) ∧
    (route x e).getLast? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)) ∧
    (route x e).Nodup ∧ (route x e).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2 ≤ (route x e).length ∧ (route x e).length ≤ 6144*(x.length+1) := by
  rcases e with (e | e) | e
  · obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatLastLinkAssembly.route_certificate x hw e
    exact ⟨hh,ht,hn,hc,hl,by change (SatLastLinkAssembly.route x e).length ≤ _; omega⟩
  · obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatVerticalDrawing.actual_route_certificate (finiteFormula x) e
    exact ⟨hh,ht,hn,hc,by change 2 ≤ (SatVerticalDrawing.route _ e).length; omega,
      by change (SatVerticalDrawing.route _ e).length ≤ _; omega⟩
  · obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatResidualDrawing.actual_route_certificate (finiteFormula x) e
    exact ⟨hh,ht,hn,hc,by change 2 ≤ (SatResidualDrawing.route _ e).length; omega,
      by change (SatResidualDrawing.route _ e).length ≤ _; omega⟩

theorem route_length_lower (x : SatTy.denote) (e : Edge x) :
    3 ≤ (route x e).length := by
  rcases e with (e | e) | e
  · exact SatLastLinkAssembly.route_length_lower x e
  · have h := (SatVerticalDrawing.route_length _ e).1
    change 3 ≤ (SatVerticalDrawing.route _ e).length
    omega
  · exact SatResidualDrawing.route_length_lower _ e

theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) (v : (SatClauseOrder.graph (finiteFormula x)).Vertex) :
    SatGlobalVertexPlacement.actualPoint (finiteFormula x) v ∈ route x e ↔
      v = source x e ∨ v = target x e := by
  rcases e with (e | e) | e
  · exact SatLastLinkAssembly.actual_vertex_clear x hw e v
  · exact SatVerticalDrawing.actual_vertex_clear _ e v
  · exact SatResidualDrawing.actual_vertex_clear _ e v

theorem endpoints_ne (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) : source x e ≠ target x e := by
  obtain ⟨hh,ht,hn,_,hl,_⟩ := route_certificate x hw e
  intro he
  rw [he] at hh
  cases hr : route x e with
  | nil => simp [hr] at hl
  | cons a l =>
    have hne : l ≠ [] := by
      intro h
      simp [hr,h] at hl
    have ha : a = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e) := by
      simpa only [hr,List.head?_cons,Option.some.injEq] using hh
    have ht' : l.getLast? = some a := by
      simpa only [hr,List.getLast?_cons_of_ne_nil hne,ha] using ht
    exact (List.nodup_cons.mp (hr ▸ hn)).1 (List.mem_of_getLast? ht')

theorem route_bounds (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) (q : Point) (hq : q ∈ route x e) :
    -128 ≤ q.1 ∧ q.1 ≤ SatVariableLattice.wireX (3*x.length)+128 ∧
      -64 ≤ q.2 ∧ q.2 ≤ SatExteriorLattice.top (3*x.length) := by
  rcases e with (e | e) | e
  · exact SatLastLinkAssembly.route_bounds x hw e q hq
  · have h := SatVerticalDrawing.route_bounds _ e q hq
    dsimp [SatVariableLattice.wireX,SatExteriorLattice.top]
    omega
  · have h := SatResidualDrawing.route_bounds _ e q hq
    dsimp [SatVariableLattice.wireX,SatExteriorLattice.top]
    omega

theorem incident_of_vertex_mem (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) (q : Point) (v : (SatClauseOrder.graph (finiteFormula x)).Vertex)
    (hv : q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v)
    (he : q ∈ route x e) : Incident x e q := by
  rw [hv] at he
  exact ((actual_vertex_clear x hw e v).mp he).imp
    (fun h => hv.trans (congrArg (SatGlobalVertexPlacement.actualPoint (finiteFormula x)) h))
    (fun h => hv.trans (congrArg (SatGlobalVertexPlacement.actualPoint (finiteFormula x)) h))

theorem intersection_of_vertex (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e f : Edge x) (q : Point)
    (hv : ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v)
    (he : q ∈ route x e) (hf : q ∈ route x f) :
    Incident x e q ∧ Incident x f q := by
  obtain ⟨v,hv⟩ := hv
  exact ⟨incident_of_vertex_mem x hw e q v hv he,incident_of_vertex_mem x hw f q v hv hf⟩

theorem residual_vertical_disjoint (x : SatTy.denote)
    (e : ResidualEdge x) (f : VerticalEdge x) :
    (SatResidualDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e).Disjoint
      (SatVerticalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :=
  SatCrossingRetirement.Residual.route_vertical_disjoint _ e f.1.val.1 f.1.val.2.1
    f.1.val.2.2 f.1.property f.2

theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e f : Edge x) (hne : e ≠ f) (q : Point)
    (he : q ∈ route x e) (hf : q ∈ route x f) :
    Incident x e q ∧ Incident x f q := by
  rcases e with (e | e) | e
  · rcases f with (f | f) | f
    · exact SatLastLinkAssembly.route_intersection x hw e f
        (fun h => hne (congrArg (fun z => Sum.inl (Sum.inl z)) h)) q he hf
    · obtain ⟨v,hv,_,_⟩ := SatVerticalCompatibility.previous_shared_vertex x hw e f q he hf
      exact intersection_of_vertex x hw _ _ q ⟨v,hv⟩ he hf
    · obtain ⟨v,hv,_,_⟩ := SatResidualCompatibility.previous_shared_vertex x hw e f q he hf
      exact intersection_of_vertex x hw _ _ q ⟨v,hv⟩ he hf
  · rcases f with (f | f) | f
    · obtain ⟨v,hv,_,_⟩ := SatVerticalCompatibility.previous_shared_vertex x hw f e q hf he
      exact intersection_of_vertex x hw _ _ q ⟨v,hv⟩ he hf
    · exact False.elim (List.disjoint_left.mp (SatVerticalDrawing.routes_disjoint _ e f
        (fun h => hne (congrArg (fun z => Sum.inl (Sum.inr z)) h))) he hf)
    · exact False.elim (List.disjoint_left.mp (residual_vertical_disjoint x f e) hf he)
  · rcases f with (f | f) | f
    · obtain ⟨v,hv,_,_⟩ := SatResidualCompatibility.previous_shared_vertex x hw f e q hf he
      exact intersection_of_vertex x hw _ _ q ⟨v,hv⟩ he hf
    · exact False.elim (List.disjoint_left.mp (residual_vertical_disjoint x e f) he hf)
    · exact False.elim (List.disjoint_left.mp (SatResidualDrawing.route_disjoint _ e f
        (fun h => hne (congrArg Sum.inr h))) he hf)

/-- All distinct indexed routes have a common point only at an actual
vertex which is an endpoint of both routes. -/
theorem shared_vertex (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e f : Edge x) (hne : e ≠ f) (q : Point)
    (he : q ∈ route x e) (hf : q ∈ route x f) :
    ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v ∧
      (v = source x e ∨ v = target x e) ∧
      (v = source x f ∨ v = target x f) := by
  have h := (route_intersection x hw e f hne q he hf).1
  rcases h with h | h
  · exact ⟨source x e,h,Or.inl rfl,(actual_vertex_clear x hw f _).mp (h ▸ hf)⟩
  · exact ⟨target x e,h,Or.inr rfl,(actual_vertex_clear x hw f _).mp (h ▸ hf)⟩

end GridHardness.SatWireDrawingGeometry
