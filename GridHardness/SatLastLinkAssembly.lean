/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetiredSideAssembly
public import GridHardness.SatLastLinkDrawing

/-!
# SAT Last Link Assembly

Add the final two row-zero links of every nonempty crossing row to the
outer, retained-cell, horizontal-connector and retired-side drawing.
All included routes meet only at actual common endpoints. Vertical
connectors and residual arcs remain outside this family.
-/

@[expose] public section

namespace GridHardness.SatLastLinkAssembly
open CliffordSynthesis CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev LinkEdge (x : SatTy.denote) :=
  SatLastLinkDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))
abbrev Edge (x : SatTy.denote) := SatRetiredSideAssembly.Edge x ⊕ LinkEdge x

noncomputable def source (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatRetiredSideAssembly.source x e
  | .inr e => SatLastLinkDrawing.source (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e

noncomputable def target (x : SatTy.denote) : Edge x →
    (SatClauseOrder.graph (finiteFormula x)).Vertex
  | .inl e => SatRetiredSideAssembly.target x e
  | .inr e => SatLastLinkDrawing.target (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e

def route (x : SatTy.denote) : Edge x → List Point
  | .inl e => SatRetiredSideAssembly.route x e
  | .inr e => SatLastLinkDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e

noncomputable def Incident (x : SatTy.denote) (e : Edge x) (q : Point) : Prop :=
  q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e) ∨
    q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)

theorem edge_is_arc (x : SatTy.denote) (e : Edge x) :
    (SatClauseOrder.graph (finiteFormula x)).adj (source x e) (target x e) := by
  cases e with
  | inl e => exact SatRetiredSideAssembly.edge_is_arc x e
  | inr e => exact SatLastLinkDrawing.edge_is_arc _ _ e

theorem route_certificate (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) :
    (route x e).head? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (source x e)) ∧
    (route x e).getLast? = some (SatGlobalVertexPlacement.actualPoint (finiteFormula x) (target x e)) ∧
    (route x e).Nodup ∧ (route x e).IsChain PlanarSatClause.Lattice.UnitStep ∧
    2 ≤ (route x e).length ∧ (route x e).length ≤ 4096*(x.length+1) := by
  cases e with
  | inl e => exact SatRetiredSideAssembly.route_certificate x hw e
  | inr e =>
    obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatLastLinkDrawing.actual_route_certificate (finiteFormula x) e
    exact ⟨hh,ht,hn,hc,by change 2 ≤ (SatLastLinkDrawing.route _ e).length; omega,
      by change (SatLastLinkDrawing.route _ e).length ≤ _; omega⟩

theorem route_length_lower (x : SatTy.denote) (e : Edge x) :
    3 ≤ (route x e).length := by
  cases e with
  | inl e => exact SatRetiredSideAssembly.route_length_lower x e
  | inr e =>
    have h := (SatLastLinkDrawing.route_certificate _ e).2.2.2.2.1
    change 3 ≤ (SatLastLinkDrawing.route _ e).length
    omega

theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : Edge x) (v : (SatClauseOrder.graph (finiteFormula x)).Vertex) :
    SatGlobalVertexPlacement.actualPoint (finiteFormula x) v ∈ route x e ↔
      v = source x e ∨ v = target x e := by
  cases e with
  | inl e => exact SatRetiredSideAssembly.actual_vertex_clear x hw e v
  | inr e => exact SatLastLinkDrawing.actual_vertex_clear _ e v

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
  | inl e => exact SatRetiredSideAssembly.route_bounds x hw e q hq
  | inr e =>
    have h := SatLastLinkDrawing.route_bounds _ e q hq
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

/-- Last-cell links lie inside the wire boxes and after the corresponding
clause link, so every outer route is disjoint from them. -/
theorem outer_link_disjoint (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatOuterDrawing.Edge x) (f : LinkEdge x) :
    (SatOuterDrawing.route x e).Disjoint
      (SatLastLinkDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) := by
  apply List.disjoint_left.mpr
  intro q he hf
  have hp : SatClauseWireSeparation.WirePoint
      (SatClauseOrder.permutation (finiteFormula x)) q :=
    .cell f.1.val (SatLastLinkDrawing.localEdge f.2) q hf
  rcases e with (e | e | e) | ⟨o,b⟩
  · cases e with
    | inl e =>
      have ho := SatVariableDrawing.route_bounds (finiteFormula x)
        (SatVariablePlacement.finite_regular x hw) e q he
      have hr := SatLastLinkDrawing.route_bounds _ f q hf
      dsimp [SatVariableLattice.wireX] at ho
      omega
    | inr e =>
      have ho := SatClauseDrawing.route_bounds e q he
      have hr := SatLastLinkDrawing.route_bounds _ f q hf
      omega
  · have ho := SatVariableChainDrawing.route_bounds e q he
    have hr := SatLastLinkDrawing.route_bounds _ f q hf
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
  · exact List.disjoint_left.mp (SatClauseRetirementClearance.last_links_disjoint
      (SatClauseOrder.permutation (finiteFormula x))
      (SatWireLayout.variableRank (finiteFormula x) o) f.1.val.1 f.1.val.2 b
      f.1.property (SatLastLinkDrawing.localEdge f.2) (SatLastLinkDrawing.localEdge_link f.2)) he hf

/-- Every horizontal connector in a row ends before its last-cell links.
Connectors in other rows have a disjoint height band. -/
theorem horizontal_link_disjoint {N : Nat} (p : Equiv.Perm (Fin N))
    (e : SatHorizontalDrawing.Edge p) (f : SatLastLinkDrawing.Edge p) :
    (SatHorizontalDrawing.route p e).Disjoint (SatLastLinkDrawing.route p f) := by
  apply List.disjoint_left.mpr
  intro q he hf
  have hb := SatCrossingHorizontal.route_bounds p e.1.val.1 e.1.val.2.1 e.1.val.2.2
    e.1.property.2.2.1 q (SatCrossingHorizontal.connectionRoute_mem _ _ _ _ e.2 q he)
  have hf' := SatCrossingLattice.route_in_box p f.1.val (SatLastLinkDrawing.localEdge f.2) q hf
  have hl := SatCrossingRetirement.Links.link_bounds p f.1.val.1 f.1.val.2
    (SatLastLinkDrawing.localEdge f.2) (SatLastLinkDrawing.localEdge_link f.2) q hf
  by_cases hj : e.1.val.2.2=f.1.val.2
  · have hm := (SatCrossingRetirement.Catalogue.lastRequest_sound p _ _ f.1.property).2
      e.1.val.2.1 (by simpa only [hj] using e.1.property.2.1)
    have hlo : PermutationWireLayout.low e.1.val.2.1 ≤ PermutationWireLayout.low f.1.val.1 := by
      dsimp [PermutationWireLayout.low]
      exact_mod_cast (show e.1.val.2.1.val+1≤f.1.val.1.val+1 by omega)
    omega
  · have hy : PermutationWireLayout.high p e.1.val.2.2 ≠
        PermutationWireLayout.high p f.1.val.2 := fun h => hj (PermutationWireLayout.high_injective p h)
    dsimp [SatCrossingLattice.InBox] at hf'
    omega

private theorem local_link_not_retained : ∀ b : Bool,
    ¬SatCrossingHorizontal.RetainedEdge (SatLastLinkDrawing.localEdge b) := by decide +kernel

/-- A last-cell link touches a retained interior route only at an actual
retained endpoint of that route, in its own crossing cell. -/
theorem retained_link_vertex (x : SatTy.denote)
    (e : SatRetainedDrawing.Edge (SatClauseOrder.permutation (finiteFormula x)))
    (f : LinkEdge x) (q : Point)
    (he : q ∈ SatRetainedDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e)
    (hf : q ∈ SatLastLinkDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v := by
  let p := SatClauseOrder.permutation (finiteFormula x)
  by_cases hc : e.1.val=f.1.val
  · have hn : e.2.val≠SatLastLinkDrawing.localEdge f.2 := by
      intro h
      exact local_link_not_retained f.2 (h ▸ e.2.property)
    obtain ⟨u,hu,hq⟩ := List.mem_map.mp he
    have hv : u ∈ XorLine.Lattice.edgeRoute (SatLastLinkDrawing.localEdge f.2) := by
      change q ∈ (XorLine.Lattice.edgeRoute (SatLastLinkDrawing.localEdge f.2)).map
        (SatCrossingLattice.frame p f.1.val).map at hf
      rw [←hq,←hc] at hf
      exact (List.mem_map_of_injective (SatCrossingLattice.frame p e.1.val).injective).mp hf
    have hi := (XorLine.Lattice.intersection_certificate e.2.val
      (SatLastLinkDrawing.localEdge f.2) hn u hu hv).1
    rcases hi with hi | hi
    · refine ⟨SatRetainedDrawing.source (finiteFormula x) p e,?_⟩
      rw [SatRetainedDrawing.source,SatRetainedDrawing.actualPoint_vertex]
      exact hq.symm.trans (congrArg (SatCrossingLattice.frame p e.1.val).map hi)
    · refine ⟨SatRetainedDrawing.target (finiteFormula x) p e,?_⟩
      rw [SatRetainedDrawing.target,SatRetainedDrawing.actualPoint_vertex]
      exact hq.symm.trans (congrArg (SatCrossingLattice.frame p e.1.val).map hi)
  · exact False.elim (List.disjoint_left.mp
      (SatCrossingLattice.distinct_cell_routes_disjoint p e.1.val f.1.val hc
        e.2.val (SatLastLinkDrawing.localEdge f.2)) he hf)

/-- A retired side can meet a last-cell link only at their common false-side
XOR port; sides from other wires are disjoint. -/
theorem side_link_vertex (x : SatTy.denote)
    (e : SatRetiredSideDrawing.Edge (SatClauseOrder.permutation (finiteFormula x)))
    (f : LinkEdge x) (q : Point)
    (he : q ∈ SatRetiredSideDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e)
    (hf : q ∈ SatLastLinkDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v := by
  by_cases hj : e.1=f.1.val.2
  · have he' : q∈SatCrossingRetirement.Sides.route
        (SatClauseOrder.permutation (finiteFormula x)) f.1.val.2 e.2 := by
      simpa only [SatRetiredSideDrawing.route,hj] using he
    obtain ⟨v,hv,_,_⟩ := SatCrossingRetirement.Sides.own_link_intersection
      (SatClauseOrder.permutation (finiteFormula x)) f.1.val.1 f.1.val.2 f.1.property
      e.2 (SatLastLinkDrawing.localEdge f.2) (SatLastLinkDrawing.localEdge_link f.2) q he' hf
    exact ⟨SatRetiredSideDrawing.vertex (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) (f.1.val.2,v),
      hv.trans (SatRetiredSideDrawing.actualPoint_vertex (finiteFormula x) (f.1.val.2,v)).symm⟩
  · exact False.elim (List.disjoint_left.mp
      (SatCrossingRetirement.Sides.other_wire_links_disjoint
        (SatClauseOrder.permutation (finiteFormula x)) e.1 f.1.val.1 f.1.val.2 hj e.2
        (SatLastLinkDrawing.localEdge f.2)) he hf)

theorem previous_link_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatRetiredSideAssembly.Edge x) (f : LinkEdge x) (q : Point)
    (he : q ∈ SatRetiredSideAssembly.route x e)
    (hf : q ∈ SatLastLinkDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    Incident x (.inl e) q ∧ Incident x (.inr f) q := by
  rcases e with ((e | e) | e) | e
  · exact False.elim (List.disjoint_left.mp (outer_link_disjoint x hw e f) he hf)
  · obtain ⟨v,hv⟩ := retained_link_vertex x e f q he hf
    exact ⟨incident_of_vertex_mem x hw (.inl (.inl (.inl (.inr e)))) q v hv he,
      incident_of_vertex_mem x hw (.inr f) q v hv hf⟩
  · exact False.elim (List.disjoint_left.mp (horizontal_link_disjoint _ e f) he hf)
  · obtain ⟨v,hv⟩ := side_link_vertex x e f q he hf
    exact ⟨incident_of_vertex_mem x hw (.inl (.inr e)) q v hv he,
      incident_of_vertex_mem x hw (.inr f) q v hv hf⟩

theorem route_intersection (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e f : Edge x) (hne : e ≠ f) (q : Point)
    (he : q ∈ route x e) (hf : q ∈ route x f) :
    Incident x e q ∧ Incident x f q := by
  rcases e with e | e
  · rcases f with f | f
    · exact SatRetiredSideAssembly.route_intersection x hw e f
        (fun h => hne (congrArg Sum.inl h)) q he hf
    · exact previous_link_intersection x hw e f q he hf
  · rcases f with f | f
    · exact (previous_link_intersection x hw f e q hf he).symm
    · exact False.elim (List.disjoint_left.mp (SatLastLinkDrawing.routes_disjoint _ e f
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

end GridHardness.SatLastLinkAssembly
