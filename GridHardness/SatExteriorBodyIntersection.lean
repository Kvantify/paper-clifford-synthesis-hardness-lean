/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatExteriorVertexClearance

/-!
# SAT Exterior Body Intersection

Intersections between the exterior and combined variable/clause
body routes are exactly shared graph endpoints.
-/

public section

namespace GridHardness.SatExteriorDrawing
open CliffordSynthesis CliffordComplexity PlanarSatAssembly
open SatExteriorLattice SatExteriorSeparation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem variable_route_incidence (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x.length) (f : SatVariableDrawing.Edge ((vsOf x).length +1))
    (q : Int × Int) (he : q ∈route x e) (hf : q ∈SatVariableDrawing.route (finiteFormula x) f) :
    Incident x e q := by
  have hr := SatVariablePlacement.finite_regular x hw
  cases e <;> simp only [route] at he
  case sentinelFirst =>
    exact False.elim (List.disjoint_left.mp (down_variable_disjoint _ hr f) he hf)
  case sentinelSecond =>
    exact False.elim (List.disjoint_left.mp (bottom_variable_disjoint _ hr f) he hf)
  case firstVariable =>
    exact Or.inr ((firstVariable_variable_boundary _ hr f q he hf).trans (first_var_point x).symm)
  case forward hm =>
    exact Or.inl ((forward_variable_boundary _ hr f q he hf).trans (last_var_point x hw).symm)
  case returning hm =>
    exact False.elim (List.disjoint_left.mp (returning_variable_disjoint _ hr f) he hf)
  case closing hm =>
    have hx : x=[] := List.length_eq_zero_iff.mp hm
    subst x
    exact Or.inl ((closing_variable_boundary _ hr f q he hf).trans (last_var_point [] hw).symm)

theorem clause_route_incidence (x : SatTy.denote) (e : Edge x.length)
    (f : SatClauseDrawing.Edge x.length) (q : Int × Int)
    (he : q ∈route x e) (hf : q ∈SatClauseDrawing.route f) : Incident x e q := by
  cases f with
  | internal c a =>
    have hb := SatClauseOrder.route_in_box c a q hf
    cases e <;> simp only [route] at he
    case sentinelFirst =>
      have h := down_clause_separation c q q he hb
      simp [IntegerGrid.manhattan] at h
    case sentinelSecond =>
      have h := bottom_clause_separation (3*x.length) c q q he hb
      simp [IntegerGrid.manhattan] at h
    case firstVariable =>
      have h := firstVariable_clause_separation (3*x.length) c q q he hb
      simp [IntegerGrid.manhattan] at h
    case forward hm =>
      obtain ⟨hc,hq⟩ := forward_clause_intersection c q he hb
      have hc' : c=CorrectedSatInterval.PermutationGraph.CoreEdges.Exterior.first hm := Fin.ext hc
      apply Or.inr
      simpa only [hc',target,SatGlobalVertexPlacement.bodyPoint] using hq
    case returning hm =>
      obtain ⟨hc,hq⟩ := returning_clause_intersection c q he hb
      have hc' : c=CorrectedSatInterval.PermutationGraph.CoreEdges.Exterior.last hm := by
        apply Fin.ext
        dsimp [CorrectedSatInterval.PermutationGraph.CoreEdges.Exterior.last]
        omega
      apply Or.inl
      simpa only [hc',source,SatGlobalVertexPlacement.bodyPoint] using hq
    case closing hm => have hc := c.isLt; omega
  | backbone c d hcd =>
    change q∈SatClauseBackbone.route c at hf
    cases e <;> simp only [route] at he
    case sentinelFirst =>
      have h := sentinel_clause_backbone_separation (3*x.length) c q q (Or.inl he) hf
      simp [IntegerGrid.manhattan] at h
    case sentinelSecond =>
      have h := sentinel_clause_backbone_separation (3*x.length) c q q (Or.inr (Or.inl he)) hf
      simp [IntegerGrid.manhattan] at h
    case firstVariable =>
      have h := sentinel_clause_backbone_separation (3*x.length) c q q (Or.inr (Or.inr he)) hf
      simp [IntegerGrid.manhattan] at h
    case forward hm =>
      exact False.elim (List.disjoint_left.mp (forward_clause_backbone_disjoint c) he hf)
    case returning hm =>
      exact False.elim (List.disjoint_left.mp (returning_clause_backbone_disjoint c d hcd) he hf)
    case closing hm => have hc := c.isLt; omega

theorem body_route_intersection (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (e : Edge x.length) (f : SatBodyDrawing.Edge ((vsOf x).length +1) x.length)
    (q : Int × Int) (he : q ∈route x e) (hf : q ∈SatBodyDrawing.route (finiteFormula x) f) :
    (q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (sourceVertex x e) ∨
      q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (targetVertex x e)) ∧
    (q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (SatBodyDrawing.source (finiteFormula x) f) ∨
      q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (SatBodyDrawing.target (finiteFormula x) f)) := by
  have hi : Incident x e q := by
    cases f with
    | inl f => exact variable_route_incidence x hw e f q he hf
    | inr f => exact clause_route_incidence x e f q he hf
  have hi' :
      q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (sourceVertex x e) ∨
      q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (targetVertex x e) := by
    simpa only [Incident,sourceVertex,targetVertex,SatGlobalVertexPlacement.actualPoint_body] using hi
  refine ⟨hi',?_⟩
  rcases hi' with hq | hq
  all_goals
    rw [hq] at hf
    have hb := (SatBodyDrawing.actual_vertex_clear (finiteFormula x)
      (SatVariablePlacement.finite_regular x hw) f _).mp hf
    exact hb.imp (fun h => hq.trans (congrArg (SatGlobalVertexPlacement.actualPoint (finiteFormula x)) h))
      (fun h => hq.trans (congrArg (SatGlobalVertexPlacement.actualPoint (finiteFormula x)) h))

end GridHardness.SatExteriorDrawing
