/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatWireDrawingArcs
public import GridHardness.DirectedIncidenceSaturation

/-!
# SAT Route Catalogue

Membership and local completeness of the actual SAT route catalogue.
The local saturation criterion reduces completeness at a wire vertex to
three distinct directed neighbors whose arcs have already been catalogued.
-/

@[expose] public section

namespace GridHardness.SatRouteCatalogue
open CliffordComplexity PlanarSatAssembly SatWireDrawingGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Vertex (x : SatTy.denote) := (SatClauseOrder.graph (finiteFormula x)).Vertex
abbrev permutation (x : SatTy.denote) := SatClauseOrder.permutation (finiteFormula x)

def Covers (x : SatTy.denote) (u v : Vertex x) : Prop :=
  ∃ e : Edge x, source x e = u ∧ target x e = v

theorem covers_arc (x : SatTy.denote) (u v : Vertex x) (h : Covers x u v) :
    (SatClauseOrder.graph (finiteFormula x)).adj u v := by
  obtain ⟨e,rfl,rfl⟩ := h
  exact edge_is_arc x e

def LocalComplete (x : SatTy.denote) (v : Vertex x) : Prop :=
  (∀ u, (SatClauseOrder.graph (finiteFormula x)).adj u v → Covers x u v) ∧
  (∀ u, (SatClauseOrder.graph (finiteFormula x)).adj v u → Covers x v u)

/-- Incoming neighbors are tagged on the left; outgoing neighbors on the right. -/
def At (x : SatTy.denote) (v : Vertex x) : Vertex x ⊕ Vertex x → Prop
  | .inl u => Covers x u v
  | .inr u => Covers x v u

theorem complete_of_three (x : SatTy.denote) (v : Vertex x)
    (w : Fin 3 → Vertex x ⊕ Vertex x) (hw : Function.Injective w)
    (hc : ∀ i, At x v (w i)) : LocalComplete x v := by
  let lift (u : Vertex x ⊕ Vertex x) (h : At x v u) :
      DirectedIncidenceSaturation.Incidence (SatClauseOrder.graph (finiteFormula x)).adj v :=
    match u with
    | .inl u => .inl ⟨u,covers_arc x u v h⟩
    | .inr u => .inr ⟨u,covers_arc x v u h⟩
  let forget : DirectedIncidenceSaturation.Incidence
      (SatClauseOrder.graph (finiteFormula x)).adj v → Vertex x ⊕ Vertex x :=
    Sum.map Subtype.val Subtype.val
  have hforget (u : Vertex x ⊕ Vertex x) (h : At x v u) : forget (lift u h) = u := by
    cases u <;> rfl
  have hclass (u : Vertex x ⊕ Vertex x) (h : At x v u) :
      DirectedIncidenceSaturation.Classified
        (SatClauseOrder.graph (finiteFormula x)).adj v (Covers x) (lift u h) := by
    cases u <;> exact h
  apply DirectedIncidenceSaturation.permutation_complete (finiteFormula x) (permutation x) v
    (fun i => lift (w i) (hc i))
  · intro i j h
    apply hw
    simpa only [hforget] using congrArg forget h
  · intro i
    exact hclass (w i) (hc i)

theorem covers_outer (x : SatTy.denote) (e : SatOuterDrawing.Edge x) :
    Covers x (SatOuterDrawing.source x e) (SatOuterDrawing.target x e) :=
  ⟨.inl (.inl (.inl (.inl (.inl (.inl e))))),rfl,rfl⟩

theorem covers_retained (x : SatTy.denote) (e : SatRetainedDrawing.Edge (permutation x)) :
    Covers x (SatRetainedDrawing.source (finiteFormula x) (permutation x) e)
      (SatRetainedDrawing.target (finiteFormula x) (permutation x) e) :=
  ⟨.inl (.inl (.inl (.inl (.inl (.inr e))))),rfl,rfl⟩

theorem covers_horizontal (x : SatTy.denote) (e : SatHorizontalDrawing.Edge (permutation x)) :
    Covers x (SatHorizontalDrawing.source (finiteFormula x) (permutation x) e)
      (SatHorizontalDrawing.target (finiteFormula x) (permutation x) e) :=
  ⟨.inl (.inl (.inl (.inl (.inr e)))),rfl,rfl⟩

theorem covers_retired (x : SatTy.denote) (e : SatRetiredSideDrawing.Edge (permutation x)) :
    Covers x (SatRetiredSideDrawing.source (finiteFormula x) (permutation x) e)
      (SatRetiredSideDrawing.target (finiteFormula x) (permutation x) e) :=
  ⟨.inl (.inl (.inl (.inr e))),rfl,rfl⟩

theorem covers_last (x : SatTy.denote) (e : SatLastLinkDrawing.Edge (permutation x)) :
    Covers x (SatLastLinkDrawing.source (finiteFormula x) (permutation x) e)
      (SatLastLinkDrawing.target (finiteFormula x) (permutation x) e) :=
  ⟨.inl (.inl (.inr e)),rfl,rfl⟩

theorem covers_vertical (x : SatTy.denote) (e : SatVerticalDrawing.Edge (permutation x)) :
    Covers x (SatVerticalDrawing.source (finiteFormula x) (permutation x) e)
      (SatVerticalDrawing.target (finiteFormula x) (permutation x) e) :=
  ⟨.inl (.inr e),rfl,rfl⟩

theorem covers_residual (x : SatTy.denote) (e : SatResidualDrawing.Edge (permutation x)) :
    Covers x (SatResidualDrawing.source (finiteFormula x) (permutation x) e)
      (SatResidualDrawing.target (finiteFormula x) (permutation x) e) :=
  ⟨.inr e,rfl,rfl⟩

end GridHardness.SatRouteCatalogue
