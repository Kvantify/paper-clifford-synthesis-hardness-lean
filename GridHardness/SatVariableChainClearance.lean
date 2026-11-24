/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableChainSeparation
public import GridHardness.SatClauseDrawing
public import GridHardness.SatExteriorDrawing
public import GridHardness.SatExteriorSeparation

/-!
# SAT Variable Chain Clearance

Clearance of the variable occurrence-chain drawing from the clause
and exterior families, and from every unrelated final graph vertex. The
exterior edge entering the first variable shares its intended endpoint
with that variable's chain-entry edge; no disjointness is claimed there.
-/

public section

namespace GridHardness.SatVariableChainClearance
open CliffordSynthesis PlanarSatAssembly SatVariableOrder SatVariableLattice
open SatVariableChainDrawing SatVariableChainSeparation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int
variable {n m : Nat}

theorem route_lower {φ : Formula n m} (e : Edge φ) (q : Point) (hq : q ∈route e) :
    128≤q.2 := by
  have hr := route_height e q hq
  have hb := owner_block_bounds e
  omega

theorem owner_positive {φ : Formula n m} (e : Edge φ) : 0<count φ (owner e) := by
  cases e with
  | entry v h => exact h
  | between v k l h => exact Nat.zero_lt_of_lt k.isLt
  | exit v h => exact h

theorem no_edge_empty_formula (φ : Formula n 0) (e : Edge φ) : False := by
  have hp := owner_positive e
  have hb := prefix_add_count_le φ (owner e)
  omega

/-- The entire clause-body and clause-backbone family lies far to the
left of every chain route. -/
theorem clause_route_separation {φ : Formula n m} (e : Edge φ)
    (f : SatClauseDrawing.Edge m) (q r : Point)
    (hq : q ∈route e) (hr : r ∈SatClauseDrawing.route f) :
    64≤IntegerGrid.manhattan q r := by
  have hc := SatClauseDrawing.route_bounds f r hr
  have hv := route_bounds e q hq
  dsimp [wireX,IntegerGrid.manhattan] at hv ⊢
  omega

theorem down_separation {φ : Formula n m} (e : Edge φ) (q r : Point)
    (hq : q ∈route e) (hr : r ∈SatExteriorLattice.down) :
    128≤IntegerGrid.manhattan q r := by
  have hc := route_lower e q hq
  have he := SatExteriorSeparation.down_support r hr
  dsimp [IntegerGrid.manhattan]
  omega

theorem bottom_separation {φ : Formula n m} (e : Edge φ) (q r : Point)
    (hq : q ∈route e) (hr : r ∈SatExteriorLattice.bottom (3 *m)) :
    192≤IntegerGrid.manhattan q r := by
  have hc := route_lower e q hq
  have he := SatExteriorSeparation.bottom_support (3*m) r hr
  dsimp [IntegerGrid.manhattan]
  omega

theorem forward_separation {φ : Formula n m} (e : Edge φ) (q r : Point)
    (hq : q ∈route e) (hr : r ∈SatExteriorLattice.forward (3 *m)) :
    64≤IntegerGrid.manhattan q r := by
  have hc := route_bounds e q hq
  have he := SatExteriorLattice.forward_support (3*m) r hr
  dsimp [wireX,SatExteriorLattice.top,IntegerGrid.manhattan] at hc he ⊢
  rcases he with he | he | he | he <;> omega

theorem returning_separation {φ : Formula n m} (e : Edge φ) (q r : Point)
    (hq : q ∈route e) (hr : r ∈SatExteriorLattice.returning (3 *m)) :
    64≤IntegerGrid.manhattan q r := by
  have hc := route_bounds e q hq
  have he := SatExteriorLattice.returning_bounds (3*m) r hr
  dsimp [wireX,IntegerGrid.manhattan] at hc ⊢
  omega

theorem closing_disjoint (φ : Formula n 0) (e : Edge φ) :
    (route e).Disjoint SatExteriorLattice.closing :=
  False.elim (no_edge_empty_formula φ e)

/-- The exterior link entering the variable list can touch a chain only
at that chain's source, which is the first variable's entry coordinate. -/
theorem firstVariable_intersection (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (e : Edge φ) (q : Point) (hq : q ∈route e)
    (hr : q ∈SatExteriorLattice.firstVariable (3 *m)) :
    q=entry (3*m) 0 ∧ q=point φ p (endpoints e).1 := by
  have hl := route_lower e q hq
  have hs := SatExteriorSeparation.firstVariable_support (3*m) q hr
  have hy : q.2=128 := by omega
  have hf : q=entry (3*m) 0 := by
    apply Prod.ext
    · exact hs.1
    · exact hy
  refine ⟨hf,?_⟩
  have hh := route_height e q hq
  cases e with
  | entry v h =>
    have hp : SatVariableOrder.prefix φ v=0 := by dsimp [interval] at hh; omega
    simpa only [endpoints,point,SatVariablePlacement.point,hp] using hf
  | between v k l h => dsimp [interval] at hh; omega
  | exit v h => dsimp [interval] at hh; omega

/-- Every exterior-family intersection is the intended endpoint shared
with the edge entering the first variable. All other cases are excluded,
including the closing edge when the formula has no clauses. -/
theorem exterior_intersection (x : CliffordComplexity.SatTy.denote)
    (e : Edge (finiteFormula x))
    (f : SatExteriorDrawing.Edge x.length) (q : Point)
    (hq : q ∈route e) (hr : q ∈SatExteriorDrawing.route x f) :
    f=.firstVariable ∧
      q=point (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) (endpoints e).1 ∧
      q=SatGlobalVertexPlacement.actualPoint (finiteFormula x) (SatExteriorDrawing.targetVertex x f) := by
  cases f with
  | sentinelFirst =>
    have h := down_separation e q q hq hr
    simp [IntegerGrid.manhattan] at h
  | sentinelSecond =>
    have h := bottom_separation e q q hq hr
    simp [IntegerGrid.manhattan] at h
  | firstVariable =>
    have h := firstVariable_intersection (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x)) e q hq hr
    refine ⟨rfl,h.2,?_⟩
    change q=SatGlobalVertexPlacement.actualPoint (finiteFormula x)
      (CorrectedSatInterval.PermutationGraph.liftOriginal (finiteFormula x)
        (SatClauseOrder.permutation (finiteFormula x)) (var (SatExteriorDrawing.firstVar x) false))
    rw [SatGlobalVertexPlacement.actualPoint_variable,SatExteriorDrawing.first_var_point]
    exact h.1
  | forward h =>
    have h := forward_separation e q q hq hr
    simp [IntegerGrid.manhattan] at h
  | returning h =>
    have h := returning_separation e q q hq hr
    simp [IntegerGrid.manhattan] at h
  | closing h =>
    have hp := owner_positive e
    have hb := prefix_add_count_le (finiteFormula x) (owner e)
    change _≤3*x.length at hb
    omega

theorem global_point_intersection (φ : Formula n m) (e : Edge φ)
    (z : SatGlobalVertexPlacement.Vertex φ)
    (hz : SatGlobalVertexPlacement.point φ z ∈route e) :
    SatGlobalVertexPlacement.point φ z=point φ (SatClauseOrder.permutation φ) (endpoints e).1 ∨
      SatGlobalVertexPlacement.point φ z=point φ (SatClauseOrder.permutation φ) (endpoints e).2 := by
  rcases z with (i | ⟨v,b⟩ | ⟨c,v⟩) | w
  · have hy := route_lower e _ hz
    fin_cases i <;> dsimp [SatGlobalVertexPlacement.point,SatGlobalVertexPlacement.bodyPoint,
      SatExteriorLattice.sentinel] at hy <;> omega
  · have hx := SatVariablePlacement.point_x φ v b
    obtain ⟨a,ha,hq⟩ := outer_boundary_intersection φ e _ hz hx
    rcases ha with ha | ha
    · exact Or.inl (hq.trans (congrArg (point φ (SatClauseOrder.permutation φ)) ha).symm)
    · exact Or.inr (hq.trans (congrArg (point φ (SatClauseOrder.permutation φ)) ha).symm)
  · have hc := SatClauseOrder.coordinates_bounded c _ (SatClauseOrder.point_in_box c v)
    have he := route_bounds e _ hz
    change wireX (3*m)≤(SatClauseOrder.point c v).1 ∧ _ at he
    dsimp [wireX] at he
    omega
  · exact wire_intersection φ (SatClauseOrder.permutation φ) e _ hz
      (SatClauseWireSeparation.WirePoint.vertex w)

/-- No unrelated vertex of the actual completed graph lies on a chain
route. Both directions use the common coordinate map and actual endpoint
identities, not a separately assumed vertex drawing. -/
theorem global_vertex_clear (φ : Formula n m) (hφ : SatVariablePlacement.Regular φ)
    (e : Edge φ) (v : (SatClauseOrder.graph φ).Vertex) :
    SatGlobalVertexPlacement.actualPoint φ v∈route e ↔
      v=vertex φ (SatClauseOrder.permutation φ) (endpoints e).1 ∨
        v=vertex φ (SatClauseOrder.permutation φ) (endpoints e).2 := by
  constructor
  · intro hv
    have h := global_point_intersection φ e ((SatGlobalVertexPlacement.equiv φ).symm v) hv
    change SatGlobalVertexPlacement.actualPoint φ v=point φ _ _ ∨
      SatGlobalVertexPlacement.actualPoint φ v=point φ _ _ at h
    rw [← actualPoint_vertex,← actualPoint_vertex] at h
    exact h.imp (fun he => SatGlobalVertexPlacement.actualPoint_injective φ hφ he)
      (fun he => SatGlobalVertexPlacement.actualPoint_injective φ hφ he)
  · rintro (rfl | rfl)
    · exact List.mem_of_head? (actual_route_endpoints φ e).1
    · exact List.mem_of_getLast? (actual_route_endpoints φ e).2

theorem finite_global_vertex_clear (x : CliffordComplexity.SatTy.denote)
    (hw : ∀ c ∈x, c.length =3) (e : Edge (finiteFormula x))
    (v : (SatClauseOrder.graph (finiteFormula x)).Vertex) :
    SatGlobalVertexPlacement.actualPoint (finiteFormula x) v∈route e ↔
      v=vertex (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) (endpoints e).1 ∨
        v=vertex (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) (endpoints e).2 :=
  global_vertex_clear (finiteFormula x) (SatVariablePlacement.finite_regular x hw) e v

end GridHardness.SatVariableChainClearance
