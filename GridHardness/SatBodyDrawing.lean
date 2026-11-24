/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatGlobalVertexPlacement
public import GridHardness.SatVariableDrawing
public import GridHardness.SatClauseDrawing

/-!
# SAT Body Drawing

Simultaneous variable and clause body routes in the common actual
vertex placement. The family includes their respective consecutive-block
backbones. It excludes sentinel links, variable-to-clause links and links
to occurrence wires, so it is not a drawing of the whole graph.
-/

@[expose] public section

namespace GridHardness.SatBodyDrawing
open CliffordSynthesis PlanarSatAssembly CorrectedSatInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
abbrev UnitStep := PlanarSatClause.Lattice.UnitStep
abbrev Edge (n m : Nat) := SatVariableDrawing.Edge n ⊕ SatClauseDrawing.Edge m

variable {n m : Nat}

def endpoints : Edge n m →
    PermutationWirePlacement.BodyVertex n m × PermutationWirePlacement.BodyVertex n m
  | .inl e => (.inr (.inl (SatVariableDrawing.endpoints e).1),
      .inr (.inl (SatVariableDrawing.endpoints e).2))
  | .inr e => (.inr (.inr (SatClauseDrawing.endpoints e).1),
      .inr (.inr (SatClauseDrawing.endpoints e).2))

def route (φ : Formula n m) : Edge n m → List Point
  | .inl e => SatVariableDrawing.route φ e
  | .inr e => SatClauseDrawing.route e

noncomputable def source (φ : Formula n m) (e : Edge n m) : (SatClauseOrder.graph φ).Vertex :=
  PermutationWirePlacement.bodyVertex φ (SatClauseOrder.permutation φ) (endpoints e).1

noncomputable def target (φ : Formula n m) (e : Edge n m) : (SatClauseOrder.graph φ).Vertex :=
  PermutationWirePlacement.bodyVertex φ (SatClauseOrder.permutation φ) (endpoints e).2

theorem source_point (φ : Formula n m) (e : Edge n m) :
    SatGlobalVertexPlacement.actualPoint φ (source φ e)=
      SatGlobalVertexPlacement.bodyPoint φ (endpoints e).1 :=
  SatGlobalVertexPlacement.actualPoint_body φ _

theorem target_point (φ : Formula n m) (e : Edge n m) :
    SatGlobalVertexPlacement.actualPoint φ (target φ e)=
      SatGlobalVertexPlacement.bodyPoint φ (endpoints e).2 :=
  SatGlobalVertexPlacement.actualPoint_body φ _

theorem edge_is_arc (φ : Formula n m) (e : Edge n m) :
    (SatClauseOrder.graph φ).adj (source φ e) (target φ e) := by
  cases e with
  | inl e => exact (SatVariableDrawing.adj_iff φ (SatClauseOrder.permutation φ)
      (SatVariableDrawing.endpoints e).1 (SatVariableDrawing.endpoints e).2).mpr ⟨e,rfl⟩
  | inr e => exact SatClauseDrawing.edge_is_arc φ e

theorem route_certificate (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e : Edge n m) :
    (route φ e).head?=some (SatGlobalVertexPlacement.actualPoint φ (source φ e)) ∧
    (route φ e).getLast?=some (SatGlobalVertexPlacement.actualPoint φ (target φ e)) ∧
    (route φ e).Nodup ∧ (route φ e).IsChain UnitStep ∧
    2≤(route φ e).length ∧ (route φ e).length≤512*(3*m)+1073 := by
  rw [source_point,target_point]
  cases e with
  | inl e =>
    obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatVariableDrawing.route_certificate φ hφ e
    exact ⟨hh,ht,hn,hc,hl,by change (SatVariableDrawing.route φ e).length≤_; omega⟩
  | inr e =>
    obtain ⟨hh,ht,hn,hc,hl,hu⟩ := SatClauseDrawing.route_certificate e
    exact ⟨hh,ht,hn,hc,hl,by change (SatClauseDrawing.route e).length≤_; omega⟩

theorem route_bounds (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e : Edge n m) (q : Point) (hq : q ∈route φ e) :
    -104≤q.1 ∧ q.1≤SatVariableLattice.wireX (3*m)+64 ∧
      0≤q.2 ∧ q.2≤1024*(3*m:Int)+516 := by
  cases e with
  | inl e =>
    have h := SatVariableDrawing.route_bounds φ hφ e q hq
    dsimp [SatVariableLattice.wireX] at h ⊢
    omega
  | inr e =>
    have h := SatClauseDrawing.route_bounds e q hq
    dsimp [SatVariableLattice.wireX]
    omega

/-- The two route families lie on opposite sides of the wire rectangle. -/
theorem variable_clause_separation (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e : SatVariableDrawing.Edge n) (f : SatClauseDrawing.Edge m) (q r : Point)
    (hq : q ∈SatVariableDrawing.route φ e) (hr : r ∈SatClauseDrawing.route f) :
    64≤IntegerGrid.manhattan q r := by
  have hv := SatVariableDrawing.route_bounds φ hφ e q hq
  have hc := SatClauseDrawing.route_bounds f r hr
  dsimp [IntegerGrid.manhattan,SatVariableLattice.wireX] at hv ⊢
  omega

theorem variable_clause_disjoint (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e : SatVariableDrawing.Edge n) (f : SatClauseDrawing.Edge m) :
    (SatVariableDrawing.route φ e).Disjoint (SatClauseDrawing.route f) := by
  apply List.disjoint_left.mpr
  intro q he hf
  have h := variable_clause_separation φ hφ e f q q he hf
  simp [IntegerGrid.manhattan] at h

/-- Distinct arcs in the combined family meet only at an endpoint of each.
The mixed case is disjoint, while each same-family case uses its established
simultaneous drawing theorem. -/
theorem route_intersection (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e f : Edge n m) (hef : e ≠f) (q : Point)
    (he : q ∈route φ e) (hf : q ∈route φ f) :
    (q=SatGlobalVertexPlacement.actualPoint φ (source φ e) ∨
      q=SatGlobalVertexPlacement.actualPoint φ (target φ e)) ∧
    (q=SatGlobalVertexPlacement.actualPoint φ (source φ f) ∨
      q=SatGlobalVertexPlacement.actualPoint φ (target φ f)) := by
  rw [source_point,target_point,source_point,target_point]
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      exact SatVariableDrawing.route_intersection φ hφ e f
        (fun h => hef (congrArg Sum.inl h)) q he hf
    | inr f =>
      exact False.elim (List.disjoint_left.mp (variable_clause_disjoint φ hφ e f) he hf)
  | inr e =>
    cases f with
    | inl f =>
      exact False.elim (List.disjoint_left.mp (variable_clause_disjoint φ hφ f e) hf he)
    | inr f =>
      exact SatClauseDrawing.route_intersection e f
        (fun h => hef (congrArg Sum.inr h)) q he hf

theorem sentinel_clear (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e : Edge n m) (i : Fin 3) : SatExteriorLattice.sentinel (3*m) i∉route φ e := by
  intro h
  have hb := route_bounds φ hφ e _ h
  fin_cases i <;> dsimp [SatExteriorLattice.sentinel,SatVariableLattice.wireX] at hb <;> omega

theorem wire_vertex_clear (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e : Edge n m) (v : SatGlobalVertexPlacement.WireVertex φ) :
    SatCrossingWireVertices.point (SatClauseOrder.permutation φ) v∉route φ e := by
  intro h
  have hw := SatCrossingWireVertices.point_bounds (SatClauseOrder.permutation φ) v
  cases e with
  | inl e =>
    have hr := SatVariableDrawing.route_bounds φ hφ e _ h
    dsimp [SatVariableLattice.wireX] at hr
    omega
  | inr e =>
    have hr := SatClauseDrawing.route_bounds e _ h
    omega

/-- Body-vertex clearance holds across the combined family, including
the sentinels and the other kind of body vertex. -/
theorem body_vertex_clear (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e : Edge n m) (v : PermutationWirePlacement.BodyVertex n m) :
    SatGlobalVertexPlacement.bodyPoint φ v∈route φ e ↔
      v=(endpoints e).1 ∨ v=(endpoints e).2 := by
  rcases v with i | ⟨v,b⟩ | ⟨c,v⟩
  · have h := sentinel_clear φ hφ e i
    cases e <;> simpa only [SatGlobalVertexPlacement.bodyPoint,endpoints,reduceCtorEq,
      or_self,iff_false] using h
  · cases e with
    | inl e =>
      simpa only [SatGlobalVertexPlacement.bodyPoint,route,endpoints,
        Sum.inr.injEq,Sum.inl.injEq,SatVariablePlacement.vertexPoint] using
        SatVariableDrawing.route_vertex_clear φ hφ e (v,b)
    | inr e =>
      simp only [endpoints,Sum.inr.injEq,reduceCtorEq,or_self,iff_false]
      intro h
      have hr := SatClauseDrawing.route_bounds e _ h
      have hv := SatVariablePlacement.point_x φ v b
      dsimp [SatVariableLattice.wireX] at hv
      dsimp only [SatGlobalVertexPlacement.bodyPoint] at hr
      omega
  · cases e with
    | inl e =>
      simp only [endpoints,Sum.inr.injEq,reduceCtorEq,or_self,iff_false]
      intro h
      have hr := SatVariableDrawing.route_bounds φ hφ e _ h
      have hc := SatClauseOrder.coordinates_bounded c _ (SatClauseOrder.point_in_box c v)
      dsimp only [SatGlobalVertexPlacement.bodyPoint,SatVariableLattice.wireX] at hr
      omega
    | inr e =>
      simpa only [SatGlobalVertexPlacement.bodyPoint,route,endpoints,
        Sum.inr.injEq,SatClauseDrawing.point] using SatClauseDrawing.route_vertex_clear e (c,v)

theorem point_vertex_clear (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e : Edge n m) (v : SatGlobalVertexPlacement.Vertex φ) :
    SatGlobalVertexPlacement.point φ v∈route φ e ↔
      v=.inl (endpoints e).1 ∨ v=.inl (endpoints e).2 := by
  cases v with
  | inl b =>
    simpa only [SatGlobalVertexPlacement.point,Sum.inl.injEq] using body_vertex_clear φ hφ e b
  | inr w =>
    simpa only [SatGlobalVertexPlacement.point,reduceCtorEq,or_self,iff_false] using
      wire_vertex_clear φ hφ e w

/-- The interiors of these routes contain no actual graph vertex from any
family, not merely no further vertex from their own body kind. -/
theorem actual_vertex_clear (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e : Edge n m) (v : (SatClauseOrder.graph φ).Vertex) :
    SatGlobalVertexPlacement.actualPoint φ v∈route φ e ↔
      v=source φ e ∨ v=target φ e := by
  obtain ⟨z,rfl⟩ := (SatGlobalVertexPlacement.equiv φ).surjective v
  rw [SatGlobalVertexPlacement.actualPoint_equiv,point_vertex_clear φ hφ]
  change _ ↔ SatGlobalVertexPlacement.equiv φ z=
    PermutationWirePlacement.bodyVertex φ (SatClauseOrder.permutation φ) (endpoints e).1 ∨
    SatGlobalVertexPlacement.equiv φ z=
      PermutationWirePlacement.bodyVertex φ (SatClauseOrder.permutation φ) (endpoints e).2
  rw [← SatGlobalVertexPlacement.equiv_body,← SatGlobalVertexPlacement.equiv_body]
  simp only [Equiv.apply_eq_iff_eq]

end GridHardness.SatBodyDrawing
