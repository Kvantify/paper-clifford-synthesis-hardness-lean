/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatHorizontalAssembly
public import GridHardness.SatRetiredSideDrawing

/-!
# SAT Retired Side Assembly

Add the six nonmandatory sides of each retired occurrence XOR to the
outer, retained-cell and horizontal-connector drawing. All included routes
meet only at actual common endpoints. Vertical connectors, residuals and
last-cell links remain outside this family.
-/

@[expose] public section

namespace GridHardness.SatRetiredSideAssembly
open CliffordSynthesis CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev SideEdge (x : SatTy.denote) :=
  SatRetiredSideDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))
abbrev Edge (x : SatTy.denote) := SatHorizontalAssembly.Edge x ⊕ SideEdge x

noncomputable def source (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatHorizontalAssembly.source x e
  | .inr e => SatRetiredSideDrawing.source (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e

noncomputable def target (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatHorizontalAssembly.target x e
  | .inr e => SatRetiredSideDrawing.target (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e

def route (x : SatTy.denote) : Edge x → List Point
  | .inl e => SatHorizontalAssembly.route x e
  | .inr e => SatRetiredSideDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e

noncomputable def Incident (x : SatTy.denote) (e : Edge x) (q : Point) : Prop :=
  q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e) ∨
    q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)

theorem edge_is_arc (x : SatTy.denote) (e : Edge x) :
    (SatClauseOrder.graph (finiteFormula x)).adj (source x e) (target x e) := by
  cases e with
  | inl e => exact SatHorizontalAssembly.edge_is_arc x e
  | inr e => exact SatRetiredSideDrawing.edge_is_arc _ _ e

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) :
    (route x e).head? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e)) ∧
    (route x e).getLast? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)) ∧
    (route x e).Nodup ∧ (route x e).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2 ≤ (route x e).length ∧ (route x e).length ≤ 4096*(x.length+1) := by
  cases e with
  | inl e => exact SatHorizontalAssembly.route_certificate x hw e
  | inr e =>
    obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatRetiredSideDrawing.actual_route_certificate (finiteFormula x) e
    exact ⟨hh,ht,hn,hc,by change 2 ≤ (SatRetiredSideDrawing.route _ e).length; omega,
      by change (SatRetiredSideDrawing.route _ e).length ≤ _; omega⟩

theorem route_length_lower (x : SatTy.denote) (e : Edge x) :
    3 ≤ (route x e).length := by
  cases e with
  | inl e => exact SatHorizontalAssembly.route_length_lower x e
  | inr e =>
    have h := (SatRetiredSideDrawing.route_certificate _ e).2.2.2.2.1
    change 3 ≤ (SatRetiredSideDrawing.route _ e).length
    omega

theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) (v : (SatClauseOrder.graph (finiteFormula x)).Vertex) :
    SatGlobalVertexPlacement.actualPoint (finiteFormula x) v ∈ route x e ↔
      v = source x e ∨ v = target x e := by
  cases e with
  | inl e => exact SatHorizontalAssembly.actual_vertex_clear x hw e v
  | inr e => exact SatRetiredSideDrawing.actual_vertex_clear _ e v

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
  | inl e => exact SatHorizontalAssembly.route_bounds x hw e q hq
  | inr e =>
    have h := SatRetiredSideDrawing.route_bounds _ e q hq
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

/-- Any intersection with an outer route is an actual vertex location.
Chains can meet a true-side port, and clause links can meet an uncrossed
false-side port. All body and exterior routes are disjoint. -/
theorem outer_side_vertex (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatOuterDrawing.Edge x) (f : SideEdge x) (q : Point)
    (he : q ∈ SatOuterDrawing.route x e)
    (hf : q ∈ SatRetiredSideDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v := by
  have hp : SatClauseWireSeparation.WirePoint
      (SatClauseOrder.permutation (finiteFormula x)) q := .side f.1 f.2 q hf
  rcases e with (e | e | e) | ⟨o,b⟩
  · cases e with
    | inl e =>
      have ho := SatVariableDrawing.route_bounds (finiteFormula x)
        (SatVariablePlacement.finite_regular x hw) e q he
      have hr := SatRetiredSideDrawing.route_bounds _ f q hf
      dsimp [SatVariableLattice.wireX] at ho
      omega
    | inr e =>
      have ho := SatClauseDrawing.route_bounds e q he
      have hr := SatRetiredSideDrawing.route_bounds _ f q hf
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
      have hi := f.1.isLt
      omega
  · have hi := SatClauseRetirementClearance.side_endpoints
      (SatClauseOrder.permutation (finiteFormula x))
      (SatWireLayout.variableRank (finiteFormula x) o) f.1 b f.2 q he hf
    have hc := SatRetiredSideDrawing.actual_route_certificate (finiteFormula x) f
    rcases hi.2 with h | h
    · exact ⟨_,Option.some.inj (h.symm.trans hc.1)⟩
    · exact ⟨_,Option.some.inj (h.symm.trans hc.2.1)⟩

theorem horizontal_side_disjoint (x : SatTy.denote)
    (e : SatHorizontalAssembly.HorizontalEdge x) (f : SideEdge x) :
    (SatHorizontalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e).Disjoint
      (SatRetiredSideDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) := by
  have h := SatCrossingRetirement.Sides.horizontal_disjoint
    (SatClauseOrder.permutation (finiteFormula x)) f.1
    e.1.val.1 e.1.val.2.1 e.1.val.2.2 f.2 e.1.property
  obtain ⟨c,b⟩ := e
  cases b
  · exact h.2.symm
  · exact h.1.symm

/-- Adding retired side arcs preserves all shared-endpoint intersection
certificates, including their contacts with chain and clause-link ports. -/
theorem previous_side_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatHorizontalAssembly.Edge x) (f : SideEdge x) (q : Point)
    (he : q ∈ SatHorizontalAssembly.route x e)
    (hf : q ∈ SatRetiredSideDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    Incident x (.inl e) q ∧ Incident x (.inr f) q := by
  rcases e with (e | e) | e
  · obtain ⟨v,hv⟩ := outer_side_vertex x hw e f q he hf
    exact ⟨incident_of_vertex_mem x hw (.inl (.inl (.inl e))) q v hv he,
      incident_of_vertex_mem x hw (.inr f) q v hv hf⟩
  · exact False.elim (List.disjoint_left.mp
      (SatRetiredSideDrawing.retained_routes_disjoint _ f e) hf he)
  · exact False.elim (List.disjoint_left.mp (horizontal_side_disjoint x e f) he hf)

theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e f : Edge x) (hne : e ≠ f) (q : Point)
    (he : q ∈ route x e) (hf : q ∈ route x f) :
    Incident x e q ∧ Incident x f q := by
  rcases e with e | e
  · rcases f with f | f
    · exact SatHorizontalAssembly.route_intersection x hw e f
        (fun h => hne (congrArg Sum.inl h)) q he hf
    · exact previous_side_intersection x hw e f q he hf
  · rcases f with f | f
    · exact (previous_side_intersection x hw f e q hf he).symm
    · exact SatRetiredSideDrawing.actual_route_intersection (finiteFormula x) e f
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

end GridHardness.SatRetiredSideAssembly
