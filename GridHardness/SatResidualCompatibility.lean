/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatResidualDrawing
public import GridHardness.SatLastLinkAssembly

/-!
# SAT Residual Compatibility

Intersections of final residual lanes with the other
route families. The statements use the common actual vertex placement; final-edge
coverage and the semantic identification of all residual arcs are separate.
-/

public section

namespace GridHardness.SatResidualCompatibility
open CliffordSynthesis CliffordComplexity PlanarSatAssembly CorrectedSatInterval
open SatCrossingRetirement SatCrossingRetirement.Segments
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev ResidualEdge (x : SatTy.denote) :=
  SatResidualDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))
variable {N n m : Nat}

theorem endpoint_vertex (φ : Formula n m)
    (e : SatResidualDrawing.Edge (SatClauseOrder.permutation φ)) (q : Point)
    (hq : (SatResidualDrawing.route (SatClauseOrder.permutation φ) e).head? = some q ∨
      (SatResidualDrawing.route (SatClauseOrder.permutation φ) e).getLast? = some q) :
    ∃ v : (SatClauseOrder.graph φ).Vertex, q = SatGlobalVertexPlacement.actualPoint φ v := by
  have he := SatResidualDrawing.actual_route_certificate φ e
  rcases hq with hq | hq
  · exact ⟨SatResidualDrawing.source φ _ e,Option.some.inj (hq.symm.trans he.1)⟩
  · exact ⟨SatResidualDrawing.target φ _ e,Option.some.inj (hq.symm.trans he.2.1)⟩

private theorem wire_vertex (φ : Formula n m)
    (v : SatCrossingWireVertices.Vertex (SatClauseOrder.permutation φ)) (q : Point)
    (hq : q = SatCrossingWireVertices.point (SatClauseOrder.permutation φ) v) :
    ∃ w : (SatClauseOrder.graph φ).Vertex, q = SatGlobalVertexPlacement.actualPoint φ w :=
  ⟨PermutationWirePlacement.vertex φ _ v,hq.trans (SatGlobalVertexPlacement.actualPoint_wire φ v).symm⟩

private theorem port_vertex (φ : Formula n m) (i j : Fin (3 *m))
    (hij : SatCrossingRouting.Active (SatClauseOrder.permutation φ) i j)
    (r : Fin 4) (upper : Bool) (q : Point)
    (hq : q = SatCrossingLattice.point (SatClauseOrder.permutation φ) (i, j)
      (if upper then SatCrossingRouting.upperPort r else SatCrossingRouting.lowerPort r)) :
    ∃ v : (SatClauseOrder.graph φ).Vertex, q = SatGlobalVertexPlacement.actualPoint φ v := by
  let w : SatCrossingHorizontal.RetainedVertex :=
    ⟨if upper then SatCrossingRouting.upperPort r else SatCrossingRouting.lowerPort r,
      by cases upper <;> dsimp [SatCrossingRouting.upperPort,SatCrossingRouting.lowerPort] <;>
        split_ifs <;> trivial⟩
  exact wire_vertex φ (.inr (⟨(i,j),hij⟩,w)) q hq

theorem retained_vertex (φ : Formula n m)
    (e : SatResidualDrawing.Edge (SatClauseOrder.permutation φ))
    (f : SatRetainedDrawing.Edge (SatClauseOrder.permutation φ)) (q : Point)
    (he : q ∈ SatResidualDrawing.route (SatClauseOrder.permutation φ) e)
    (hf : q ∈ SatRetainedDrawing.route (SatClauseOrder.permutation φ) f) :
    ∃ v : (SatClauseOrder.graph φ).Vertex, q = SatGlobalVertexPlacement.actualPoint φ v := by
  rcases e with ⟨i,r,part⟩
  have hl := Residual.rowEnd_valid (SatClauseOrder.permutation φ) i
  cases part with
  | unsplit h =>
    exact False.elim (List.disjoint_left.mp (whole_retained_route_clear _ _ i hl h r
      f.1.val f.1.property f.2.val f.2.property.1 f.2.property.2) he hf)
  | above j hj =>
    have h := upper_retained_route_clear _ _ i j hl hj r f.1.val f.1.property
      f.2.val f.2.property.1 f.2.property.2 q he hf
    exact port_vertex φ i j hj.1 r false q h.2
  | below j hj =>
    have h := lower_route_clear _ _ i j (Catalogue.last_before _ i) hj r
      f.1.val f.1.property f.2.val q he hf
    exact port_vertex φ i j hj.1 r true q h.2

theorem horizontal_vertex (φ : Formula n m)
    (e : SatResidualDrawing.Edge (SatClauseOrder.permutation φ))
    (f : SatHorizontalDrawing.Edge (SatClauseOrder.permutation φ)) (q : Point)
    (he : q ∈ SatResidualDrawing.route (SatClauseOrder.permutation φ) e)
    (hf : q ∈ SatHorizontalDrawing.route (SatClauseOrder.permutation φ) f) :
    ∃ v : (SatClauseOrder.graph φ).Vertex, q = SatGlobalVertexPlacement.actualPoint φ v := by
  rcases f with ⟨c,b⟩
  cases b
  · have h := (Residual.route_lower_intersection_iff _ e c.val.1 c.val.2.1
      c.val.2.2 c.property q).mp ⟨he,hf⟩
    refine ⟨SatHorizontalDrawing.target φ _ (c,false),?_⟩
    rw [SatHorizontalDrawing.target,SatRetainedDrawing.actualPoint_vertex]
    exact h.2.2.2
  · have h := (Residual.route_upper_intersection_iff _ e c.val.1 c.val.2.1
      c.val.2.2 c.property q).mp ⟨he,hf⟩
    refine ⟨SatHorizontalDrawing.source φ _ (c,true),?_⟩
    rw [SatHorizontalDrawing.source,SatRetainedDrawing.actualPoint_vertex]
    exact h.2.2.2

theorem side_vertex (φ : Formula n m)
    (e : SatResidualDrawing.Edge (SatClauseOrder.permutation φ))
    (f : SatRetiredSideDrawing.Edge (SatClauseOrder.permutation φ)) (q : Point)
    (he : q ∈ SatResidualDrawing.route (SatClauseOrder.permutation φ) e)
    (hf : q ∈ SatRetiredSideDrawing.route (SatClauseOrder.permutation φ) f) :
    ∃ v : (SatClauseOrder.graph φ).Vertex, q = SatGlobalVertexPlacement.actualPoint φ v := by
  by_cases h : f.1=e.1
  · rcases f with ⟨i,s⟩
    dsimp at h
    subst i
    exact endpoint_vertex φ e q
      (Sides.same_wire_residual_endpoints _ e.1 s e.2.1 e.2.2 q hf he).2
  · exact False.elim (List.disjoint_left.mp
      (Sides.other_wire_residual_disjoint _ f.1 f.2 e h) hf he)

theorem link_vertex (φ : Formula n m)
    (e : SatResidualDrawing.Edge (SatClauseOrder.permutation φ))
    (f : SatLastLinkDrawing.Edge (SatClauseOrder.permutation φ)) (q : Point)
    (he : q ∈ SatResidualDrawing.route (SatClauseOrder.permutation φ) e)
    (hf : q ∈ SatLastLinkDrawing.route (SatClauseOrder.permutation φ) f) :
    ∃ v : (SatClauseOrder.graph φ).Vertex, q = SatGlobalVertexPlacement.actualPoint φ v := by
  rcases e with ⟨i,r,part⟩
  have hl := Residual.rowEnd_valid (SatClauseOrder.permutation φ) i
  have hd := (SatLastLinkDrawing.cell f).property
  change SatCrossingRouting.Active (SatClauseOrder.permutation φ) f.1.val.1 f.1.val.2 at hd
  change q ∈ SatCrossingLattice.route (SatClauseOrder.permutation φ)
    (f.1.val.1,f.1.val.2) (SatLastLinkDrawing.localEdge f.2) at hf
  have hb := SatCrossingLattice.route_in_box _ f.1.val (SatLastLinkDrawing.localEdge f.2) q hf
  by_cases hown : Residual.rowEnd (SatClauseOrder.permutation φ) i = some f.1.val.1 ∧ f.1.val.2=i
  · have hwhole := Residual.path_subset _ _ i (Catalogue.last_before _ i) r part he
    change q ∈ Placement.route _ (Residual.rowEnd _ i) i r at hwhole
    rw [hown.1] at hwhole
    have hf' : q ∈ SatCrossingLattice.route (SatClauseOrder.permutation φ)
        (f.1.val.1,i) (SatLastLinkDrawing.localEdge f.2) := by simpa only [hown.2] using hf
    have hai : f.1.val.1 < i := by simpa only [hown.2] using hd.1
    have h := Links.whole_link_intersection _ f.1.val.1 i hai r
      (SatLastLinkDrawing.localEdge f.2) (SatLastLinkDrawing.localEdge_link f.2) q hwhole hf'
    apply wire_vertex φ (.inl (i,falseVertex r)) q
    change q = Placement.point _ (Residual.rowEnd _ i) i (falseVertex r)
    rw [hown.1]
    exact h.1
  · have hprev : Residual.rowEnd (SatClauseOrder.permutation φ) i ≠ some f.1.val.1 ∨
        f.1.val.2 ≠ i := by tauto
    cases part with
    | unsplit h =>
      exact False.elim (whole_other_box_clear _ _ i hl h r f.1.val hd hprev q he hb)
    | above j hj =>
      by_cases hc : f.1.val=(i,j)
      · have heq := (upper_endpoint_box _ _ i j (Catalogue.last_before _ i) hj.1 r q he).mp
          (hc ▸ hb)
        apply port_vertex φ i j hj.1 r false q
        simpa only [Bool.false_eq_true,ite_false,SatCrossingRouting.lowerPort_coordinates] using heq
      · exact False.elim (upper_other_box_clear _ _ i j hl hj r f.1.val hd hc hprev q he hb)
    | below j hj =>
      have h := lower_box_clear _ _ i j (Catalogue.last_before _ i) hj r f.1.val hd q he hb
      apply port_vertex φ i j hj.1 r true q
      simpa only [ite_true,SatCrossingRouting.upperPort_coordinates] using h.2

theorem outer_vertex (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatOuterDrawing.Edge x) (f : ResidualEdge x) (q : Point)
    (he : q ∈ SatOuterDrawing.route x e)
    (hf : q ∈ SatResidualDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v := by
  have hp : SatClauseWireSeparation.WirePoint
      (SatClauseOrder.permutation (finiteFormula x)) q := .residual f q hf
  rcases e with (e | e | e) | ⟨o,b⟩
  · cases e with
    | inl e =>
      have ho := SatVariableDrawing.route_bounds (finiteFormula x)
        (SatVariablePlacement.finite_regular x hw) e q he
      have hr := SatResidualDrawing.route_bounds _ f q hf
      dsimp [SatVariableLattice.wireX] at ho
      omega
    | inr e =>
      have ho := SatClauseDrawing.route_bounds e q he
      have hr := SatResidualDrawing.route_bounds _ f q hf
      omega
  · have h := SatVariableChainDrawing.wire_intersection (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e q he hp
    rcases h with h | h
    · exact ⟨SatVariableChainDrawing.vertex (finiteFormula x) _
        (SatVariableChainDrawing.endpoints e).1,
        h.trans (SatVariableChainDrawing.actualPoint_vertex (finiteFormula x) _).symm⟩
    · exact ⟨SatVariableChainDrawing.vertex (finiteFormula x) _
        (SatVariableChainDrawing.endpoints e).2,
        h.trans (SatVariableChainDrawing.actualPoint_vertex (finiteFormula x) _).symm⟩
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
  · exact endpoint_vertex (finiteFormula x) f q
      (SatClauseRetirementClearance.residual_endpoints
        (SatClauseOrder.permutation (finiteFormula x))
        (SatWireLayout.variableRank (finiteFormula x) o) b f q he hf).2

/-- Every mixed intersection is a shared actual endpoint, for all outer,
retained, horizontal, retired-side and last-link routes at once. -/
theorem previous_shared_vertex (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatLastLinkAssembly.Edge x) (f : ResidualEdge x) (q : Point)
    (he : q ∈ SatLastLinkAssembly.route x e)
    (hf : q ∈ SatResidualDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v ∧
      (v = SatLastLinkAssembly.source x e ∨ v = SatLastLinkAssembly.target x e) ∧
      (v = SatResidualDrawing.source (finiteFormula x)
          (SatClauseOrder.permutation (finiteFormula x)) f ∨
        v = SatResidualDrawing.target (finiteFormula x)
          (SatClauseOrder.permutation (finiteFormula x)) f) := by
  have hv : ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v := by
    rcases e with (((e | e) | e) | e) | e
    · exact outer_vertex x hw e f q he hf
    · exact retained_vertex (finiteFormula x) f e q hf he
    · exact horizontal_vertex (finiteFormula x) f e q hf he
    · exact side_vertex (finiteFormula x) f e q hf he
    · exact link_vertex (finiteFormula x) f e q hf he
  obtain ⟨v,hv⟩ := hv
  exact ⟨v,hv,(SatLastLinkAssembly.actual_vertex_clear x hw e v).mp (hv ▸ he),
    (SatResidualDrawing.actual_vertex_clear (finiteFormula x) f v).mp (hv ▸ hf)⟩

end GridHardness.SatResidualCompatibility
