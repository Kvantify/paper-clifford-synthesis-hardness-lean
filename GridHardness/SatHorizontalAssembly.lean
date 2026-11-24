/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatOuterRetainedDrawing
public import GridHardness.SatHorizontalDrawing

/-!
# SAT Horizontal Assembly

Simultaneous routes for the outer SAT arcs, retained crossing interiors,
and both horizontal connectors between consecutive crossing columns.
Vertical connectors, retired side arcs, residuals and last-cell links are
outside this family. Every included mixed intersection is a shared endpoint.
-/

@[expose] public section

namespace GridHardness.SatHorizontalAssembly
open CliffordSynthesis CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev HorizontalEdge (x : SatTy.denote) :=
  SatHorizontalDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))
abbrev Edge (x : SatTy.denote) := SatOuterRetainedDrawing.Edge x ⊕ HorizontalEdge x

noncomputable def source (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatOuterRetainedDrawing.source x e
  | .inr e => SatHorizontalDrawing.source (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e

noncomputable def target (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatOuterRetainedDrawing.target x e
  | .inr e => SatHorizontalDrawing.target (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e

def route (x : SatTy.denote) : Edge x → List Point
  | .inl e => SatOuterRetainedDrawing.route x e
  | .inr e => SatHorizontalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e

noncomputable def Incident (x : SatTy.denote) (e : Edge x) (q : Point) : Prop :=
  q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e) ∨
    q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)

theorem edge_is_arc (x : SatTy.denote) (e : Edge x) :
    (SatClauseOrder.graph (finiteFormula x)).adj (source x e) (target x e) := by
  cases e with
  | inl e => exact SatOuterRetainedDrawing.edge_is_arc x e
  | inr e => exact SatHorizontalDrawing.edge_is_arc _ _ e

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) :
    (route x e).head? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e)) ∧
    (route x e).getLast? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)) ∧
    (route x e).Nodup ∧ (route x e).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2 ≤ (route x e).length ∧ (route x e).length ≤ 4096*(x.length+1) := by
  cases e with
  | inl e => exact SatOuterRetainedDrawing.route_certificate x hw e
  | inr e =>
    obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatHorizontalDrawing.actual_route_certificate (finiteFormula x) e
    exact ⟨hh,ht,hn,hc,by change 2 ≤ (SatHorizontalDrawing.route _ e).length; omega,
      by change (SatHorizontalDrawing.route _ e).length ≤ _; omega⟩

theorem route_length_lower (x : SatTy.denote) (e : Edge x) :
    3 ≤ (route x e).length := by
  cases e with
  | inl e => exact SatOuterRetainedDrawing.route_length_lower x e
  | inr e =>
    have h := (SatHorizontalDrawing.route_length _ e).1
    change 3 ≤ (SatHorizontalDrawing.route _ e).length
    omega

theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) (v : (SatClauseOrder.graph (finiteFormula x)).Vertex) :
    SatGlobalVertexPlacement.actualPoint (finiteFormula x) v ∈ route x e ↔
      v = source x e ∨ v = target x e := by
  cases e with
  | inl e => exact SatOuterRetainedDrawing.actual_vertex_clear x hw e v
  | inr e => exact SatHorizontalDrawing.actual_vertex_clear _ e v

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
  cases e with
  | inl e => exact SatOuterRetainedDrawing.route_bounds x hw e q hq
  | inr e =>
    have h := SatHorizontalDrawing.route_bounds _ e q hq
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

/-- Horizontal connectors remain strictly inside the wire region and begin
after each row's clause link. They cannot touch any outer SAT route. -/
theorem outer_horizontal_disjoint (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatOuterDrawing.Edge x) (f : HorizontalEdge x) :
    (SatOuterDrawing.route x e).Disjoint
      (SatHorizontalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) := by
  apply List.disjoint_left.mpr
  intro q he hf
  have hp : SatClauseWireSeparation.WirePoint
      (SatClauseOrder.permutation (finiteFormula x)) q :=
    .horizontal f.1.val.1 f.1.val.2.1 f.1.val.2.2 f.1.property.2.2.1 q
      (SatCrossingHorizontal.connectionRoute_mem _ _ _ _ f.2 q hf)
  rcases e with (e | e | e) | ⟨o,b⟩
  · cases e with
    | inl e =>
      have ho := SatVariableDrawing.route_bounds (finiteFormula x)
        (SatVariablePlacement.finite_regular x hw) e q he
      have hr := SatHorizontalDrawing.route_bounds _ f q hf
      dsimp [SatVariableLattice.wireX] at ho
      omega
    | inr e =>
      have ho := SatClauseDrawing.route_bounds e q he
      have hr := SatHorizontalDrawing.route_bounds _ f q hf
      omega
  · have ho := SatVariableChainDrawing.route_bounds e q he
    have hr := SatHorizontalDrawing.route_bounds _ f q hf
    dsimp [SatVariableLattice.wireX] at ho
    omega
  · cases e with
    | sentinelFirst =>
      have h := SatExteriorSeparation.down_wire_separation
        (SatClauseOrder.permutation (finiteFormula x)) q q he hp
      simp [IntegerGrid.manhattan] at h
    | sentinelSecond =>
      have h := SatExteriorSeparation.bottom_wire_separation
        (SatClauseOrder.permutation (finiteFormula x)) q q he hp
      simp [IntegerGrid.manhattan] at h
    | firstVariable =>
      have h := SatExteriorSeparation.firstVariable_wire_separation
        (SatClauseOrder.permutation (finiteFormula x)) q q he hp
      simp [IntegerGrid.manhattan] at h
    | forward hm =>
      have h := SatExteriorLattice.forward_wire_separation
        (SatClauseOrder.permutation (finiteFormula x)) q q he hp
      simp [IntegerGrid.manhattan] at h
    | returning hm =>
      have h := SatExteriorLattice.returning_wire_separation
        (SatClauseOrder.permutation (finiteFormula x)) q q he hp
      simp [IntegerGrid.manhattan] at h
    | closing hm =>
      have hi := f.1.val.1.isLt
      omega
  · exact SatClauseWireConnectorClearance.horizontal_clear
      (SatClauseOrder.permutation (finiteFormula x))
      (SatWireLayout.variableRank (finiteFormula x) o)
      f.1.val.1 f.1.val.2.1 f.1.val.2.2 b f.2 f.1.property q he hf

/-- Mixed intersections with the assembled family can only occur in a
retained crossing, at the connector's designated local port. -/
theorem previous_horizontal_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatOuterRetainedDrawing.Edge x) (f : HorizontalEdge x) (q : Point)
    (he : q ∈ SatOuterRetainedDrawing.route x e)
    (hf : q ∈ SatHorizontalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    Incident x (.inl e) q ∧ Incident x (.inr f) q := by
  cases e with
  | inl e => exact False.elim (List.disjoint_left.mp (outer_horizontal_disjoint x hw e f) he hf)
  | inr e =>
    obtain ⟨v,_,_,hv⟩ := SatHorizontalDrawing.retained_shared_vertex (finiteFormula x) f e q hf he
    exact ⟨incident_of_vertex_mem x hw (.inl (.inr e)) q v hv he,
      incident_of_vertex_mem x hw (.inr f) q v hv hf⟩

theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e f : Edge x) (hne : e ≠ f) (q : Point)
    (he : q ∈ route x e) (hf : q ∈ route x f) :
    Incident x e q ∧ Incident x f q := by
  rcases e with e | e
  · rcases f with f | f
    · exact SatOuterRetainedDrawing.route_intersection x hw e f
        (fun h => hne (congrArg Sum.inl h)) q he hf
    · exact previous_horizontal_intersection x hw e f q he hf
  · rcases f with f | f
    · exact (previous_horizontal_intersection x hw f e q hf he).symm
    · exact False.elim (List.disjoint_left.mp (SatHorizontalDrawing.routes_disjoint _ e f
        (fun h => hne (congrArg Sum.inr h))) he hf)

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

end GridHardness.SatHorizontalAssembly
