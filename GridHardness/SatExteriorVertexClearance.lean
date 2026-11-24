/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatExteriorIntersection
public import GridHardness.SatBodyDrawing

/-!
# SAT Exterior Vertex Clearance

Exterior routes avoid every unrelated vertex of the final graph.
All endpoint identities refer to the common simultaneous placement.
-/

public section

namespace GridHardness.SatExteriorDrawing
open CliffordSynthesis CliffordComplexity PlanarSatAssembly
open SatExteriorLattice SatExteriorSeparation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem route_bounds (x : SatTy.denote) (e : Edge x.length) (q : Int × Int)
    (hq : q ∈route x e) :
    -128≤q.1 ∧ q.1≤SatVariableLattice.wireX (3*x.length)+128 ∧
      -64≤q.2 ∧ q.2≤top (3*x.length) := by
  cases e <;> simp only [route] at hq
  case sentinelFirst =>
    have h := down_support q hq
    dsimp [SatVariableLattice.wireX,top]
    omega
  case sentinelSecond =>
    have h := bottom_support (3*x.length) q hq
    dsimp [top]
    omega
  case firstVariable =>
    have h := firstVariable_support (3*x.length) q hq
    dsimp [SatVariableLattice.wireX,top] at h ⊢
    omega
  case forward hm =>
    have h := forward_bounds (3*x.length) q hq
    omega
  case returning hm =>
    have h := returning_bounds (3*x.length) q hq
    dsimp [SatVariableLattice.wireX,top]
    omega
  case closing hm =>
    have h := closing_support q hq
    simp only [hm,Nat.mul_zero]
    dsimp [SatVariableLattice.wireX,top]
    rcases h with h | h | h | h | h <;> omega

theorem sentinel_intersection (x : SatTy.denote) (e : Edge x.length) (i : Fin 3)
    (hi : sentinel (3 *x.length) i ∈route x e) :
    Incident x e (sentinel (3*x.length) i) := by
  cases e <;> simp only [route] at hi
  case sentinelFirst =>
    have h := down_support _ hi
    fin_cases i <;> simp [Incident,source,target,SatGlobalVertexPlacement.bodyPoint]
    dsimp [sentinel,SatVariableLattice.wireX] at h
    omega
  case sentinelSecond =>
    have h := bottom_support (3*x.length) _ hi
    fin_cases i <;> simp [Incident,source,target,SatGlobalVertexPlacement.bodyPoint]
    dsimp [sentinel] at h
    omega
  case firstVariable =>
    have h := firstVariable_support (3*x.length) _ hi
    fin_cases i <;> simp [Incident,source,target,SatGlobalVertexPlacement.bodyPoint]
    all_goals dsimp [sentinel,SatVariableLattice.wireX] at h; omega
  case forward hm =>
    have h := forward_support (3*x.length) _ hi
    fin_cases i <;> dsimp [sentinel,top] at h
    all_goals rcases h with h | h | h | h <;> omega
  case returning hm =>
    have h := returning_bounds (3*x.length) _ hi
    fin_cases i <;> simp [Incident,source,target,SatGlobalVertexPlacement.bodyPoint]
    all_goals dsimp [sentinel,SatVariableLattice.wireX] at h; omega
  case closing hm =>
    have h := closing_support _ hi
    fin_cases i <;> simp [Incident,source,target,SatGlobalVertexPlacement.bodyPoint]
    all_goals dsimp [sentinel] at h
    all_goals rcases h with h | h | h | h | h <;> omega

theorem variable_intersection (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x.length) (v : Fin ((vsOf x).length +1)) (b : Bool)
    (hv : SatVariablePlacement.point (finiteFormula x) v b ∈route x e) :
    Incident x e (SatVariablePlacement.point (finiteFormula x) v b) := by
  have hr := SatVariablePlacement.finite_regular x hw
  have hb : SatVariablePlacement.point (finiteFormula x) v b∈
      SatVariableDrawing.route (finiteFormula x) (.direct v) := by
    cases b
    · exact List.mem_of_head? (SatVariableDrawing.route_certificate _ hr (.direct v)).1
    · exact List.mem_of_getLast? (SatVariableDrawing.route_certificate _ hr (.direct v)).2.1
  cases e <;> simp only [route] at hv
  case sentinelFirst =>
    exact False.elim (List.disjoint_left.mp (down_variable_disjoint _ hr (.direct v)) hv hb)
  case sentinelSecond =>
    exact False.elim (List.disjoint_left.mp (bottom_variable_disjoint _ hr (.direct v)) hv hb)
  case firstVariable =>
    apply Or.inr
    exact (firstVariable_variable_boundary _ hr (.direct v) _ hv hb).trans (first_var_point x).symm
  case forward hm =>
    apply Or.inl
    exact (forward_variable_boundary _ hr (.direct v) _ hv hb).trans (last_var_point x hw).symm
  case returning hm =>
    exact False.elim (List.disjoint_left.mp (returning_variable_disjoint _ hr (.direct v)) hv hb)
  case closing hm =>
    have hx : x=[] := List.length_eq_zero_iff.mp hm
    subst x
    apply Or.inl
    exact (closing_variable_boundary _ hr (.direct v) _ hv hb).trans (last_var_point [] hw).symm

theorem clause_intersection (x : SatTy.denote) (e : Edge x.length)
    (c : Fin x.length) (v : Fin 12)
    (hv : SatClauseOrder.point c v ∈route x e) :
    Incident x e (SatClauseOrder.point c v) := by
  have hb := SatClauseOrder.point_in_box c v
  cases e <;> simp only [route] at hv
  case sentinelFirst =>
    have h := down_clause_separation c _ _ hv hb
    simp [IntegerGrid.manhattan] at h
  case sentinelSecond =>
    have h := bottom_clause_separation (3*x.length) c _ _ hv hb
    simp [IntegerGrid.manhattan] at h
  case firstVariable =>
    have h := firstVariable_clause_separation (3*x.length) c _ _ hv hb
    simp [IntegerGrid.manhattan] at h
  case forward hm =>
    obtain ⟨hc,hp⟩ := forward_clause_intersection c _ hv hb
    have he : c=CorrectedSatInterval.PermutationGraph.CoreEdges.Exterior.first hm := by
      apply Fin.ext
      exact hc
    apply Or.inr
    simpa only [he,target,source,SatGlobalVertexPlacement.bodyPoint] using hp
  case returning hm =>
    obtain ⟨hc,hp⟩ := returning_clause_intersection c _ hv hb
    have he : c=CorrectedSatInterval.PermutationGraph.CoreEdges.Exterior.last hm := by
      apply Fin.ext
      dsimp [CorrectedSatInterval.PermutationGraph.CoreEdges.Exterior.last]
      omega
    apply Or.inl
    simpa only [he,target,source,SatGlobalVertexPlacement.bodyPoint] using hp
  case closing hm => have hc := c.isLt; omega

theorem wire_vertex_clear (x : SatTy.denote) (e : Edge x.length)
    (w : SatGlobalVertexPlacement.WireVertex (finiteFormula x)) :
    SatCrossingWireVertices.point (SatClauseOrder.permutation (finiteFormula x)) w∉route x e := by
  intro hw
  have hp := SatClauseWireSeparation.WirePoint.vertex w
  cases e <;> simp only [route] at hw
  case sentinelFirst =>
    have h := down_wire_separation (SatClauseOrder.permutation (finiteFormula x)) _ _ hw hp
    simp [IntegerGrid.manhattan] at h
  case sentinelSecond =>
    have h := bottom_wire_separation (SatClauseOrder.permutation (finiteFormula x)) _ _ hw hp
    simp [IntegerGrid.manhattan] at h
  case firstVariable =>
    have h := firstVariable_wire_separation (SatClauseOrder.permutation (finiteFormula x)) _ _ hw hp
    simp [IntegerGrid.manhattan] at h
  case forward hm =>
    have h := forward_wire_separation (SatClauseOrder.permutation (finiteFormula x)) _ _ hw hp
    simp [IntegerGrid.manhattan] at h
  case returning hm =>
    have h := returning_wire_separation (SatClauseOrder.permutation (finiteFormula x)) _ _ hw hp
    simp [IntegerGrid.manhattan] at h
  case closing hm =>
    rcases w with ⟨j,v⟩ | ⟨⟨⟨i,j⟩,hc⟩,v⟩
    · have hj := j.isLt; omega
    · have hi := i.isLt; omega

theorem global_point_intersection (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x.length) (z : SatGlobalVertexPlacement.Vertex (finiteFormula x))
    (hz : SatGlobalVertexPlacement.point (finiteFormula x) z ∈route x e) :
    Incident x e (SatGlobalVertexPlacement.point (finiteFormula x) z) := by
  rcases z with (i | ⟨v,b⟩ | ⟨c,v⟩) | w
  · exact sentinel_intersection x e i hz
  · exact variable_intersection x hw e v b hz
  · exact clause_intersection x e c v hz
  · exact False.elim (wire_vertex_clear x e w hz)

/-- No vertex of any family lies in the interior of an exterior route. -/
theorem actual_vertex_clear (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x.length) (v : (SatClauseOrder.graph (finiteFormula x)).Vertex) :
    SatGlobalVertexPlacement.actualPoint (finiteFormula x) v∈route x e ↔
      v=sourceVertex x e ∨ v=targetVertex x e := by
  constructor
  · intro hv
    have h := global_point_intersection x hw e
      ((SatGlobalVertexPlacement.equiv (finiteFormula x)).symm v) hv
    change SatGlobalVertexPlacement.actualPoint (finiteFormula x) v=
      SatGlobalVertexPlacement.bodyPoint (finiteFormula x) (source x e) ∨
      SatGlobalVertexPlacement.actualPoint (finiteFormula x) v=
        SatGlobalVertexPlacement.bodyPoint (finiteFormula x) (target x e) at h
    rw [← SatGlobalVertexPlacement.actualPoint_body,
      ← SatGlobalVertexPlacement.actualPoint_body] at h
    exact h.imp (fun he => SatGlobalVertexPlacement.finite_actualPoint_injective x hw he)
      (fun he => SatGlobalVertexPlacement.finite_actualPoint_injective x hw he)
  · rintro (rfl | rfl)
    · exact List.mem_of_head? (route_endpoints x hw e).1
    · exact List.mem_of_getLast? (route_endpoints x hw e).2

end GridHardness.SatExteriorDrawing
