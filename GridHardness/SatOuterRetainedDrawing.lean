/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatOuterDrawing
public import GridHardness.SatRetainedDrawing

/-!
# SAT Outer Retained Drawing

Simultaneous graph routes for outer SAT arcs and retained internal
crossing edges, including all mixed intersections between those families.
Intercell connectors and retired-wire arcs are handled by separate drawing
modules and combined in `SatWireDrawingGeometry`.
-/

@[expose] public section

namespace GridHardness.SatOuterRetainedDrawing
open CliffordSynthesis CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev RetainedEdge (x : SatTy.denote) :=
  SatRetainedDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))
abbrev Edge (x : SatTy.denote) := SatOuterDrawing.Edge x ⊕ RetainedEdge x

noncomputable def source (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatOuterDrawing.source x e
  | .inr e => SatRetainedDrawing.source (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e

noncomputable def target (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatOuterDrawing.target x e
  | .inr e => SatRetainedDrawing.target (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e

def route (x : SatTy.denote) : Edge x → List Point
  | .inl e => SatOuterDrawing.route x e
  | .inr e => SatRetainedDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e

noncomputable def Incident (x : SatTy.denote) (e : Edge x) (q : Point) : Prop :=
  q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e) ∨
    q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)

theorem edge_is_arc (x : SatTy.denote) (e : Edge x) :
    (SatClauseOrder.graph (finiteFormula x)).adj (source x e) (target x e) := by
  cases e with
  | inl e => exact SatOuterDrawing.edge_is_arc x e
  | inr e => exact SatRetainedDrawing.edge_is_arc _ _ e

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) :
    (route x e).head? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e)) ∧
    (route x e).getLast? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)) ∧
    (route x e).Nodup ∧ (route x e).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2 ≤ (route x e).length ∧ (route x e).length ≤ 4096*(x.length+1) := by
  cases e with
  | inl e => exact SatOuterDrawing.route_certificate x hw e
  | inr e =>
    obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatRetainedDrawing.actual_route_certificate (finiteFormula x) e
    exact ⟨hh,ht,hn,hc,hl,by change (SatRetainedDrawing.route _ e).length ≤ _; omega⟩

theorem route_length_lower (x : SatTy.denote) (e : Edge x) :
    3 ≤ (route x e).length := by
  cases e with
  | inl e => have h := SatOuterDrawing.route_length_lower x e; change 3 ≤ (SatOuterDrawing.route x e).length; omega
  | inr e => exact SatRetainedDrawing.route_length_lower _ e

theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) (v : (SatClauseOrder.graph (finiteFormula x)).Vertex) :
    SatGlobalVertexPlacement.actualPoint (finiteFormula x) v ∈ route x e ↔
      v = source x e ∨ v = target x e := by
  cases e with
  | inl e => exact SatOuterDrawing.actual_vertex_clear x hw e v
  | inr e => exact SatRetainedDrawing.actual_vertex_clear _ e v

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
  | inl e => exact SatOuterDrawing.route_bounds x hw e q hq
  | inr e =>
    have h := SatRetainedDrawing.route_bounds _ e q hq
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

/-- Every mixed intersection is the location of an actual graph vertex.
Body and exterior routes are separated from retained cells; chains and
clause links can touch them only at their designated wire endpoints. -/
theorem outer_retained_vertex (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatOuterDrawing.Edge x) (f : RetainedEdge x) (q : Point)
    (he : q ∈ SatOuterDrawing.route x e)
    (hf : q ∈ SatRetainedDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v := by
  have hp : SatClauseWireSeparation.WirePoint
      (SatClauseOrder.permutation (finiteFormula x)) q :=
    .cell f.1.val f.2.val q hf
  rcases e with (e | e | e) | ⟨o,b⟩
  · cases e with
    | inl e =>
      have ho := SatVariableDrawing.route_bounds (finiteFormula x)
        (SatVariablePlacement.finite_regular x hw) e q he
      have hr := SatRetainedDrawing.route_bounds _ f q hf
      dsimp [SatVariableLattice.wireX] at ho
      omega
    | inr e =>
      have ho := SatClauseDrawing.route_bounds e q he
      have hr := SatRetainedDrawing.route_bounds _ f q hf
      omega
  · have hi := SatVariableChainDrawing.wire_intersection (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e q he hp
    rcases hi with hi | hi
    · exact ⟨_,hi.trans (SatVariableChainDrawing.actualPoint_vertex _ _).symm⟩
    · exact ⟨_,hi.trans (SatVariableChainDrawing.actualPoint_vertex _ _).symm⟩
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
  · have hi := SatClauseWireLattice.active_box_intersection
      (SatClauseOrder.permutation (finiteFormula x)) (SatWireLayout.variableRank (finiteFormula x) o)
      b f.1.val f.1.property q he
      (SatCrossingLattice.route_in_box _ f.1.val f.2.val q hf)
    exact ⟨SatClauseWireDrawing.actualWireVertex (finiteFormula x) o b,
      hi.2.2.trans (SatClauseWireDrawing.actualPoint_actualWireVertex _ _ _).symm⟩

theorem outer_retained_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatOuterDrawing.Edge x) (f : RetainedEdge x) (q : Point)
    (he : q ∈ SatOuterDrawing.route x e)
    (hf : q ∈ SatRetainedDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    Incident x (.inl e) q ∧ Incident x (.inr f) q := by
  obtain ⟨v,hv⟩ := outer_retained_vertex x hw e f q he hf
  exact ⟨incident_of_vertex_mem x hw (.inl e) q v hv he,
    incident_of_vertex_mem x hw (.inr f) q v hv hf⟩

/-- Every same-family and mixed-family pair meets only at shared endpoints. -/
theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e f : Edge x) (hne : e ≠ f) (q : Point)
    (he : q ∈ route x e) (hf : q ∈ route x f) :
    Incident x e q ∧ Incident x f q := by
  rcases e with e | e
  · rcases f with f | f
    · exact SatOuterDrawing.route_intersection x hw e f
        (fun h => hne (congrArg Sum.inl h)) q he hf
    · exact outer_retained_intersection x hw e f q he hf
  · rcases f with f | f
    · exact (outer_retained_intersection x hw f e q hf he).symm
    · exact SatRetainedDrawing.actual_route_intersection (finiteFormula x) e f
        (fun h => hne (congrArg Sum.inr h)) q he hf

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

end GridHardness.SatOuterRetainedDrawing
