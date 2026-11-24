/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVerticalDrawingCode

/-!
# SAT Intercell Catalogue Code

The SAT-fed horizontal and vertical record programs enumerate their
exact portions of the complete route catalogue, with its original labels.
-/

@[expose] public section

namespace GridHardness.SatIntercellCatalogueCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

abbrev Edge (x : SatTy.denote) := SatHorizontalDrawingCode.Edge x ⊕ SatVerticalDrawingCode.Edge x
abbrev RoutesTy := DirectedRouteLookupCode.RecordsTy

def horizontalIndex (x : SatTy.denote) (e : SatHorizontalDrawingCode.Edge x) :
    SatWireDrawingGeometry.Edge x := .inl (.inl (.inl (.inl (.inr e))))

def verticalIndex (x : SatTy.denote) (e : SatVerticalDrawingCode.Edge x) :
    SatWireDrawingGeometry.Edge x := .inl (.inr e)

def catalogueIndex (x : SatTy.denote) : Edge x → SatWireDrawingGeometry.Edge x
  | .inl e => horizontalIndex x e
  | .inr e => verticalIndex x e

noncomputable def catalogueRecord (x : SatTy.denote) (e : SatWireDrawingGeometry.Edge x) :
    DirectedRouteLookupCode.RecordTy.denote :=
  ((SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.source x e),
      SatClauseBodyCode.actualLabel x (SatWireDrawingGeometry.target x e)),
    (SatWireDrawingGeometry.route x e).map encodePoint)

theorem horizontal_record (x : SatTy.denote) (e : SatHorizontalDrawingCode.Edge x) :
    SatHorizontalDrawingCode.routeRecord x e=catalogueRecord x (horizontalIndex x e) := rfl

theorem vertical_record (x : SatTy.denote) (e : SatVerticalDrawingCode.Edge x) :
    SatVerticalDrawingCode.routeRecord x e=catalogueRecord x (verticalIndex x e) := rfl

def routes : Code SatTy RoutesTy :=
  Code.append SatHorizontalDrawingCode.routes SatVerticalDrawingCode.routes

attribute [local irreducible] SatHorizontalCode.records SatVerticalCode.records
  SatHorizontalDrawingCode.recordAt SatVerticalDrawingCode.recordAt

theorem mem_routes (x : SatTy.denote) (r : DirectedRouteLookupCode.RecordTy.denote) :
    r∈routes.eval x ↔ ∃ e : Edge x, catalogueRecord x (catalogueIndex x e)=r := by
  rw [routes, append_eval, List.mem_append,SatHorizontalDrawingCode.mem_routes,
    SatVerticalDrawingCode.mem_routes]
  constructor
  · rintro (⟨e,he⟩ | ⟨e,he⟩)
    · exact ⟨.inl e,he⟩
    · exact ⟨.inr e,he⟩
  · rintro ⟨e,he⟩
    cases e with
    | inl e => exact Or.inl ⟨e,he⟩
    | inr e => exact Or.inr ⟨e,he⟩

theorem catalogue_covered (x : SatTy.denote) (e : Edge x) :
    catalogueRecord x (catalogueIndex x e)∈routes.eval x := (mem_routes x _).mpr ⟨e,rfl⟩

theorem emitted_arc (x : SatTy.denote) (e : Edge x) :
    (SatClauseOrder.graph (finiteFormula x)).adj
      (SatWireDrawingGeometry.source x (catalogueIndex x e))
      (SatWireDrawingGeometry.target x (catalogueIndex x e)) := by
  cases e with
  | inl e => exact SatHorizontalDrawing.edge_is_arc _ _ e
  | inr e => exact SatVerticalDrawing.edge_is_arc _ _ e

theorem route_certificate (x : SatTy.denote) (e : Edge x) :
    (SatWireDrawingGeometry.route x (catalogueIndex x e)).Nodup ∧
      (SatWireDrawingGeometry.route x (catalogueIndex x e)).IsChain XorLine.Lattice.UnitStep ∧
      2≤(SatWireDrawingGeometry.route x (catalogueIndex x e)).length ∧
      (SatWireDrawingGeometry.route x (catalogueIndex x e)).length≤1536*x.length := by
  cases e with
  | inl e =>
    have hs := SatHorizontalDrawing.route_simple (SatClauseOrder.permutation (finiteFormula x)) e
    have hl := SatHorizontalDrawing.route_length (SatClauseOrder.permutation (finiteFormula x)) e
    refine ⟨hs.1,hs.2,?_,?_⟩
    · change 2≤(SatHorizontalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e).length
      omega
    · change (SatHorizontalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e).length≤_
      nlinarith [hl.2]
  | inr e =>
    have hs := SatVerticalDrawing.route_simple (SatClauseOrder.permutation (finiteFormula x)) e
    have hl := SatVerticalDrawing.route_length (SatClauseOrder.permutation (finiteFormula x)) e
    refine ⟨hs.1,hs.2,?_,?_⟩
    · change 2≤(SatVerticalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e).length
      omega
    · change (SatVerticalDrawing.route (SatClauseOrder.permutation (finiteFormula x)) e).length≤_
      nlinarith [hl.2]

/-- The whole intercell catalogue has at most quadratically many records. -/
theorem routes_length_le (x : SatTy.denote) : (routes.eval x).length≤54*x.length*x.length := by
  have hh : (SatHorizontalDrawingCode.routes.eval x).length=(SatHorizontalCode.records.eval x).length := by
    rw [SatHorizontalDrawingCode.routes]
    exact List.length_map (f := fun a => SatHorizontalDrawingCode.recordAt.eval (x,a))
      (as := SatHorizontalCode.records.eval x)
  have hv : (SatVerticalDrawingCode.routes.eval x).length=(SatVerticalCode.records.eval x).length := by
    rw [SatVerticalDrawingCode.routes]
    exact List.length_map (f := fun a => SatVerticalDrawingCode.recordAt.eval (x,a))
      (as := SatVerticalCode.records.eval x)
  rw [routes, append_eval, List.length_append,hh,hv]
  have hb := SatHorizontalCode.records_length_le x
  have vb := SatVerticalCode.records_length_le x
  nlinarith

end GridHardness.SatIntercellCatalogueCode
