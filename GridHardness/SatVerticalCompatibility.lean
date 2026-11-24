/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVerticalDrawing
public import GridHardness.SatLastLinkAssembly
public import GridHardness.SatCrossingRoutingSeparation

/-!
# SAT Vertical Compatibility

Compatibility of the four vertical row lanes with the existing outer,
retained-cell, horizontal, retired-side, and last-cell-link families. Every
intersection is a common endpoint in the actual vertex placement. These
geometric statements do not assume that the vertical endpoint pairs have
already been identified with final-graph arcs.
-/

public section

namespace GridHardness.SatVerticalCompatibility
open CliffordSynthesis CliffordComplexity PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev VerticalEdge (x : SatTy.denote) :=
  SatVerticalDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))

variable {N n m : Nat}

theorem outer_disjoint (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatOuterDrawing.Edge x) (f : VerticalEdge x) :
    (SatOuterDrawing.route x e).Disjoint
      (SatVerticalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) := by
  apply List.disjoint_left.mpr
  intro q he hf
  have hp : SatClauseWireSeparation.WirePoint
      (SatClauseOrder.permutation (finiteFormula x)) q :=
    .vertical f.1.val.1 f.1.val.2.1 f.1.val.2.2 f.2 f.1.property.2.2.1 q hf
  rcases e with (e | e | e) | ⟨o,b⟩
  · cases e with
    | inl e =>
      have ho := SatVariableDrawing.route_bounds (finiteFormula x)
        (SatVariablePlacement.finite_regular x hw) e q he
      have hr := SatVerticalDrawing.route_bounds _ f q hf
      dsimp [SatVariableLattice.wireX] at ho
      omega
    | inr e =>
      have ho := SatClauseDrawing.route_bounds e q he
      have hr := SatVerticalDrawing.route_bounds _ f q hf
      omega
  · have ho := SatVariableChainDrawing.route_bounds e q he
    have hr := SatVerticalDrawing.route_bounds _ f q hf
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
  · exact SatClauseWireConnectorClearance.vertical_clear
      (SatClauseOrder.permutation (finiteFormula x))
      (SatWireLayout.variableRank (finiteFormula x) o)
      f.1.val.1 f.1.val.2.1 f.1.val.2.2 b f.2 f.1.property q he hf

theorem side_disjoint (p : Equiv.Perm (Fin N))
    (e : SatRetiredSideDrawing.Edge p) (f : SatVerticalDrawing.Edge p) :
    (SatRetiredSideDrawing.route p e).Disjoint (SatVerticalDrawing.route p f) :=
  SatCrossingRetirement.Sides.vertical_disjoint p e.1 f.1.val.1 f.1.val.2.1
    f.1.val.2.2 e.2 f.2 f.1.property

/-- Local routes of every active cell can meet a vertical connector only
at one of the connector's two boundary vertices. No retention restriction
is needed, so this also covers the final row-zero links. -/
theorem cell_intersection (p : Equiv.Perm (Fin N)) (e : SatVerticalDrawing.Edge p)
    (c : WireCrossingSchedule.Cell p) (f : Fin 66) (q : Point)
    (he : q ∈ SatVerticalDrawing.route p e) (hf : q ∈ SatCrossingLattice.route p c.val f) :
    q = SatRetainedDrawing.point p (SatVerticalDrawing.endpoints e).1 ∨
    q = SatRetainedDrawing.point p (SatVerticalDrawing.endpoints e).2 := by
  have h := (SatCrossingRouting.edge_intersection_iff p e.1.val.1 e.1.val.2.1
    e.1.val.2.2 e.1.property e.2 c.val c.property f q).mp ⟨he,hf⟩
  rcases h with ⟨_,h,_⟩ | ⟨_,h,_⟩
  · by_cases hr : e.2.val%2=0
    · apply Or.inr
      simpa only [SatCrossingRouting.lowerPort,hr,ite_true,SatVerticalDrawing.endpoints,
        SatRetainedDrawing.point,SatVerticalDrawing.lowerCell,SatVerticalDrawing.inputPort] using h
    · apply Or.inl
      simpa only [SatCrossingRouting.lowerPort,hr,ite_false,SatVerticalDrawing.endpoints,
        SatRetainedDrawing.point,SatVerticalDrawing.lowerCell,SatVerticalDrawing.outputPort] using h
  · by_cases hr : e.2.val%2=0
    · apply Or.inl
      simpa only [SatCrossingRouting.upperPort,hr,ite_true,SatVerticalDrawing.endpoints,
        SatRetainedDrawing.point,SatVerticalDrawing.upperCell,SatVerticalDrawing.outputPort] using h
    · apply Or.inr
      simpa only [SatCrossingRouting.upperPort,hr,ite_false,SatVerticalDrawing.endpoints,
        SatRetainedDrawing.point,SatVerticalDrawing.upperCell,SatVerticalDrawing.inputPort] using h

theorem link_vertex (φ : Formula n m)
    (e : SatLastLinkDrawing.Edge (SatClauseOrder.permutation φ))
    (f : SatVerticalDrawing.Edge (SatClauseOrder.permutation φ)) (q : Point)
    (he : q ∈ SatLastLinkDrawing.route (SatClauseOrder.permutation φ) e)
    (hf : q ∈ SatVerticalDrawing.route (SatClauseOrder.permutation φ) f) :
    ∃ v : (SatClauseOrder.graph φ).Vertex, q = SatGlobalVertexPlacement.actualPoint φ v := by
  have h := cell_intersection (SatClauseOrder.permutation φ) f
    (SatLastLinkDrawing.cell e) (SatLastLinkDrawing.localEdge e.2) q hf he
  rcases h with h | h
  · exact ⟨SatVerticalDrawing.source φ (SatClauseOrder.permutation φ) f,
      h.trans (SatRetainedDrawing.actualPoint_vertex φ _).symm⟩
  · exact ⟨SatVerticalDrawing.target φ (SatClauseOrder.permutation φ) f,
      h.trans (SatRetainedDrawing.actualPoint_vertex φ _).symm⟩

theorem horizontal_vertex (φ : Formula n m)
    (e : SatHorizontalDrawing.Edge (SatClauseOrder.permutation φ))
    (f : SatVerticalDrawing.Edge (SatClauseOrder.permutation φ)) (q : Point)
    (he : q ∈ SatHorizontalDrawing.route (SatClauseOrder.permutation φ) e)
    (hf : q ∈ SatVerticalDrawing.route (SatClauseOrder.permutation φ) f) :
    ∃ v : (SatClauseOrder.graph φ).Vertex, q = SatGlobalVertexPlacement.actualPoint φ v := by
  obtain ⟨c,b⟩ := e
  cases b
  · have h := (SatCrossingRoutingSeparation.lower_intersection_iff
      (SatClauseOrder.permutation φ) c.val.1 c.val.2.1 c.val.2.2
      f.1.val.1 f.1.val.2.1 f.1.val.2.2 f.2 c.property f.1.property q).mp ⟨he,hf⟩
    refine ⟨SatHorizontalDrawing.target φ (SatClauseOrder.permutation φ) (c,false),?_⟩
    rw [SatHorizontalDrawing.target,SatRetainedDrawing.actualPoint_vertex]
    exact h.2.2.2
  · have h := (SatCrossingRoutingSeparation.upper_intersection_iff
      (SatClauseOrder.permutation φ) c.val.1 c.val.2.1 c.val.2.2
      f.1.val.1 f.1.val.2.1 f.1.val.2.2 f.2 c.property f.1.property q).mp ⟨he,hf⟩
    refine ⟨SatHorizontalDrawing.source φ (SatClauseOrder.permutation φ) (c,true),?_⟩
    rw [SatHorizontalDrawing.source,SatRetainedDrawing.actualPoint_vertex]
    exact h.2.2.2

/-- A mixed intersection with any edge of the other route families is the image
of a vertex common to the two endpoint pairs. -/
theorem previous_shared_vertex (x : SatTy.denote) (hw : ∀ c ∈ x, c.length = 3)
    (e : SatLastLinkAssembly.Edge x) (f : VerticalEdge x) (q : Point)
    (he : q ∈ SatLastLinkAssembly.route x e)
    (hf : q ∈ SatVerticalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) f) :
    ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v ∧
      (v = SatLastLinkAssembly.source x e ∨ v = SatLastLinkAssembly.target x e) ∧
      (v = SatVerticalDrawing.source (finiteFormula x)
          (SatClauseOrder.permutation (finiteFormula x)) f ∨
        v = SatVerticalDrawing.target (finiteFormula x)
          (SatClauseOrder.permutation (finiteFormula x)) f) := by
  have hv : ∃ v : (SatClauseOrder.graph (finiteFormula x)).Vertex,
      q = SatGlobalVertexPlacement.actualPoint (finiteFormula x) v := by
    rcases e with (((e | e) | e) | e) | e
    · exact False.elim (List.disjoint_left.mp (outer_disjoint x hw e f) he hf)
    · obtain ⟨v,_,_,hv⟩ := SatVerticalDrawing.retained_shared_vertex
        (finiteFormula x) f e q hf he
      exact ⟨v,hv⟩
    · exact horizontal_vertex (finiteFormula x) e f q he hf
    · exact False.elim (List.disjoint_left.mp (side_disjoint _ e f) he hf)
    · exact link_vertex (finiteFormula x) e f q he hf
  obtain ⟨v,hv⟩ := hv
  exact ⟨v,hv,(SatLastLinkAssembly.actual_vertex_clear x hw e v).mp (hv ▸ he),
    (SatVerticalDrawing.actual_vertex_clear (finiteFormula x) f v).mp (hv ▸ hf)⟩

end GridHardness.SatVerticalCompatibility
