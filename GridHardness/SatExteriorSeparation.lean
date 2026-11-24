/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatExteriorLattice
public import GridHardness.SatVariableDrawing

/-!
# SAT Exterior Separation

Clearance of the exterior and sentinel routes from the already
drawn variable and clause bodies. Boundary intersections use the actual
first and last slots of the encoded formula, including its unused slot.
-/

public section

namespace GridHardness.SatExteriorSeparation
open CliffordSynthesis PlanarSatAssembly SatVariableLattice SatExteriorLattice
open SatVariablePlacement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int

variable {n m N : Nat}

theorem down_support (q : Point) (hq : q ∈down) :
    q.1=-128 ∧ -64≤q.2 ∧ q.2≤0 := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range] at hk
  dsimp [downPoint]
  omega

theorem bottom_support (N : Nat) (q : Point) (hq : q ∈bottom N) :
    q.2=-64 ∧ -128≤q.1 ∧ q.1≤wireX N+64 := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_range] at hk
  dsimp [bottomPoint,wireX]
  omega

theorem firstVariable_support (N : Nat) (q : Point) (hq : q ∈firstVariable N) :
    q.1=wireX N+64 ∧ -64≤q.2 ∧ q.2≤128 := by
  rw [firstVariable,SatCrossingRouting.rising_mem] at hq
  exact ⟨hq.1,by omega,by omega⟩

theorem variable_point_lower (φ : Formula n m) (v : Fin n) (b : Bool) :
    128≤(point φ v b).2 := by
  have h := point_between φ v b
  change (entry (3*m) (SatVariableOrder.prefix φ v)).2≤_ ∧ _ at h
  dsimp [entry,entryY] at h
  omega

theorem variable_route_lower (φ : Formula n m) (hφ : Regular φ)
    (e : SatVariableDrawing.Edge n) (q : Point) (hq : q ∈SatVariableDrawing.route φ e) :
    128≤q.2 := by
  have hr := (SatVariableDrawing.route_mem φ hφ e q).mp hq
  have hl := variable_point_lower φ (SatVariableDrawing.endpoints e).1.1
    (SatVariableDrawing.endpoints e).1.2
  change 128≤(vertexPoint φ (SatVariableDrawing.endpoints e).1).2 at hl
  omega

/-- The exterior forward link touches the variable strip only at its
starting point at the upper end of the unused final block. -/
theorem forward_variable_boundary (φ : Formula n m) (hφ : Regular φ)
    (e : SatVariableDrawing.Edge n) (q : Point)
    (hf : q ∈forward (3 *m)) (hv : q ∈SatVariableDrawing.route φ e) :
    q=emptyExit (3*m) (3*m) := by
  have hs := forward_support (3*m) q hf
  have hb := SatVariableDrawing.route_bounds φ hφ e q hv
  rcases hs with hs | hs | hs | hs
  · apply Prod.ext <;> dsimp [emptyExit,entryY] <;> omega
  · omega
  · dsimp [top] at hs
    omega
  · dsimp [wireX] at hb
    omega

theorem returning_variable_disjoint (φ : Formula n m) (hφ : Regular φ)
    (e : SatVariableDrawing.Edge n) :
    (returning (3*m)).Disjoint (SatVariableDrawing.route φ e) := by
  apply List.disjoint_left.mpr
  intro q hr hv
  have hb := SatVariableDrawing.route_bounds φ hφ e q hv
  have hs := returning_bounds (3*m) q hr
  dsimp [wireX] at hb
  omega

theorem down_variable_disjoint (φ : Formula n m) (hφ : Regular φ)
    (e : SatVariableDrawing.Edge n) :
    down.Disjoint (SatVariableDrawing.route φ e) := by
  apply List.disjoint_left.mpr
  intro q hd hv
  have hs := down_support q hd
  have hb := variable_route_lower φ hφ e q hv
  omega

theorem bottom_variable_disjoint (φ : Formula n m) (hφ : Regular φ)
    (e : SatVariableDrawing.Edge n) :
    (bottom (3*m)).Disjoint (SatVariableDrawing.route φ e) := by
  apply List.disjoint_left.mpr
  intro q hd hv
  have hs := bottom_support (3*m) q hd
  have hb := variable_route_lower φ hφ e q hv
  omega

theorem firstVariable_variable_boundary (φ : Formula n m) (hφ : Regular φ)
    (e : SatVariableDrawing.Edge n) (q : Point)
    (hf : q ∈firstVariable (3 *m)) (hv : q ∈SatVariableDrawing.route φ e) :
    q=entry (3*m) 0 := by
  have hs := firstVariable_support (3*m) q hf
  have hb := variable_route_lower φ hφ e q hv
  apply Prod.ext <;> dsimp [entry,entryY] <;> omega

theorem finite_last_point (x : CliffordComplexity.SatTy.denote)
    (hw : ∀ c ∈x, c.length =3) :
    point (finiteFormula x) (SatVariableOrder.Finite.lastSlot x) true=
      emptyExit (3*x.length) (3*x.length) := by
  simp [point,SatVariableOrder.Finite.count_last_zero x hw,
    SatVariableOrder.Finite.last_prefix x hw]

/-- For valid encoded inputs the forward link meets only the direct
edge of the final unused variable, at that edge's target. -/
theorem forward_variable_intersection (x : CliffordComplexity.SatTy.denote)
    (hw : ∀ c ∈x, c.length =3)
    (e : SatVariableDrawing.Edge ((CliffordComplexity.vsOf x).length +1)) (q : Point)
    (hf : q ∈forward (3 *x.length)) (hv : q ∈SatVariableDrawing.route (finiteFormula x) e) :
    e=.direct (SatVariableOrder.Finite.lastSlot x) ∧
      q=point (finiteFormula x) (SatVariableOrder.Finite.lastSlot x) true := by
  have hq := (forward_variable_boundary (finiteFormula x) (finite_regular x hw) e q hf hv).trans
    (finite_last_point x hw).symm
  refine ⟨?_,hq⟩
  rw [hq] at hv
  have he := (SatVariableDrawing.route_vertex_clear (finiteFormula x) (finite_regular x hw)
    e (SatVariableOrder.Finite.lastSlot x,true)).mp hv
  cases e with
  | direct v =>
    simp [SatVariableDrawing.endpoints] at he
    exact congrArg SatVariableDrawing.Edge.direct he.symm
  | backbone v w h =>
    simp [SatVariableDrawing.endpoints] at he
    have hv := congrArg Fin.val he
    dsimp [SatVariableOrder.Finite.lastSlot] at hv
    have hw' := w.isLt
    omega

theorem first_point (φ : Formula n m) (hn : 0 <n) :
    point φ ⟨0,hn⟩ false=entry (3*m) 0 := by
  simp [point,SatVariableOrder.prefix,SatVariableOrder.offset]

theorem firstVariable_variable_intersection (φ : Formula n m) (hφ : Regular φ)
    (hn : 0 <n) (e : SatVariableDrawing.Edge n) (q : Point)
    (hf : q ∈firstVariable (3 *m)) (hv : q ∈SatVariableDrawing.route φ e) :
    e=.direct ⟨0,hn⟩ ∧ q=point φ ⟨0,hn⟩ false := by
  have hq := (firstVariable_variable_boundary φ hφ e q hf hv).trans (first_point φ hn).symm
  refine ⟨?_,hq⟩
  rw [hq] at hv
  have he := (SatVariableDrawing.route_vertex_clear φ hφ e (⟨0,hn⟩,false)).mp hv
  cases e with
  | direct v =>
    simp [SatVariableDrawing.endpoints] at he
    exact congrArg SatVariableDrawing.Edge.direct he.symm
  | backbone v w h =>
    simp [SatVariableDrawing.endpoints] at he
    have hv := congrArg Fin.val he
    change 0=w.val at hv
    omega

theorem down_wire_separation (p : Equiv.Perm (Fin N)) (q r : Point)
    (hq : q ∈down) (hr : SatClauseWireSeparation.WirePoint p r) :
    128≤IntegerGrid.manhattan q r := by
  have hs := down_support q hq
  have hb := SatClauseWireSeparation.wire_bounds p r hr
  dsimp [IntegerGrid.manhattan]
  omega

theorem bottom_wire_separation (p : Equiv.Perm (Fin N)) (q r : Point)
    (hq : q ∈bottom N) (hr : SatClauseWireSeparation.WirePoint p r) :
    64≤IntegerGrid.manhattan q r := by
  have hs := bottom_support N q hq
  have hb := SatClauseWireSeparation.wire_bounds p r hr
  dsimp [IntegerGrid.manhattan]
  omega

theorem firstVariable_wire_separation (p : Equiv.Perm (Fin N)) (q r : Point)
    (hq : q ∈firstVariable N) (hr : SatClauseWireSeparation.WirePoint p r) :
    64≤IntegerGrid.manhattan q r := by
  have hs := firstVariable_support N q hq
  have hb := SatClauseWireSeparation.wire_bounds p r hr
  dsimp [IntegerGrid.manhattan,wireX] at hs ⊢
  omega

theorem down_clause_separation (c : Fin m) (q r : Point)
    (hq : q ∈down) (hr : SatClauseOrder.InBox c r) :
    24≤IntegerGrid.manhattan q r := by
  have hs := down_support q hq
  have hb := SatClauseOrder.coordinates_bounded c r hr
  dsimp [IntegerGrid.manhattan]
  omega

theorem bottom_clause_separation (N : Nat) (c : Fin m) (q r : Point)
    (hq : q ∈bottom N) (hr : SatClauseOrder.InBox c r) :
    64≤IntegerGrid.manhattan q r := by
  have hs := bottom_support N q hq
  have hb := SatClauseOrder.coordinates_bounded c r hr
  dsimp [IntegerGrid.manhattan]
  omega

theorem firstVariable_clause_separation (N : Nat) (c : Fin m) (q r : Point)
    (hq : q ∈firstVariable N) (hr : SatClauseOrder.InBox c r) :
    64≤IntegerGrid.manhattan q r := by
  have hs := firstVariable_support N q hq
  have hb := SatClauseOrder.coordinates_bounded c r hr
  dsimp [IntegerGrid.manhattan,wireX] at hs ⊢
  omega

theorem down_bottom_intersection (N : Nat) (q : Point)
    (hd : q ∈down) (hb : q ∈bottom N) : q=sentinel N 1 := by
  have hd' := down_support q hd
  have hb' := bottom_support N q hb
  apply Prod.ext <;> simp [sentinel] <;> omega

theorem bottom_firstVariable_intersection (N : Nat) (q : Point)
    (hb : q ∈bottom N) (hf : q ∈firstVariable N) : q=sentinel N 2 := by
  have hb' := bottom_support N q hb
  have hf' := firstVariable_support N q hf
  apply Prod.ext <;> simp [sentinel] <;> omega

theorem down_firstVariable_disjoint (N : Nat) : down.Disjoint (firstVariable N) := by
  apply List.disjoint_left.mpr
  intro q hd hf
  have hd' := down_support q hd
  have hf' := firstVariable_support N q hf
  dsimp [wireX] at hf'
  omega

theorem forward_clause_internal_intersection (c : Fin m) (e : Fin 14) (q : Point)
    (hf : q ∈forward (3 *m)) (he : q ∈SatClauseOrder.route c e) :
    c.val=0 ∧ q=SatClauseOrder.point c 8 ∧
      (8=(PlanarSatClause.Lattice.edge e).1 ∨ 8=(PlanarSatClause.Lattice.edge e).2) := by
  obtain ⟨hc,hq⟩ := forward_clause_intersection c q hf (SatClauseOrder.route_in_box c e q he)
  refine ⟨hc,hq,?_⟩
  rw [hq] at he
  exact (SatClausePlacement.route_vertex_clear (Fin.rev c) e 8).mp he

theorem returning_clause_internal_intersection (c : Fin m) (e : Fin 14) (q : Point)
    (hf : q ∈returning (3 *m)) (he : q ∈SatClauseOrder.route c e) :
    c.val+1=m ∧ q=SatClauseOrder.point c 1 ∧
      (1=(PlanarSatClause.Lattice.edge e).1 ∨ 1=(PlanarSatClause.Lattice.edge e).2) := by
  obtain ⟨hc,hq⟩ := returning_clause_intersection c q hf (SatClauseOrder.route_in_box c e q he)
  refine ⟨hc,hq,?_⟩
  rw [hq] at he
  exact (SatClausePlacement.route_vertex_clear (Fin.rev c) e 1).mp he

theorem forward_clause_backbone_disjoint (c : Fin m) :
    (forward (3*m)).Disjoint (SatClauseBackbone.route c) := by
  apply List.disjoint_left.mpr
  intro q hf hc
  have hs := forward_support (3*m) q hf
  have hb := (SatClauseBackbone.route_mem c q).mp hc
  dsimp [SatClauseBackbone.OnRoute] at hb
  rw [SatClauseOrder.base_eq] at hb
  dsimp [wireX,top] at hs
  rcases hs with hs | hs | hs | hs <;> omega

/-- Only genuine links to a following clause are included; the last
clause has no clause-to-clause backbone edge. -/
theorem returning_clause_backbone_disjoint (c d : Fin m) (hcd : d.val =c.val +1) :
    (returning (3*m)).Disjoint (SatClauseBackbone.route c) := by
  apply List.disjoint_left.mpr
  intro q hr hc
  have hs := returning_support (3*m) q hr
  have hb := (SatClauseBackbone.route_mem c q).mp hc
  have hd := d.isLt
  dsimp [SatClauseBackbone.OnRoute] at hb
  rw [SatClauseOrder.base_eq] at hb
  rcases hs with hs | hs <;> omega

theorem sentinel_clause_backbone_separation (N : Nat) (c : Fin m) (q r : Point)
    (hq : q ∈down ∨ q ∈bottom N ∨ q ∈firstVariable N)
    (hr : r ∈SatClauseBackbone.route c) : 64≤IntegerGrid.manhattan q r := by
  have hb := SatClauseBackbone.coordinates_bounded c r hr
  rcases hq with hq | hq | hq
  · have hs := down_support q hq
    dsimp [IntegerGrid.manhattan]
    omega
  · have hs := bottom_support N q hq
    dsimp [IntegerGrid.manhattan]
    omega
  · have hs := firstVariable_support N q hq
    dsimp [IntegerGrid.manhattan,wireX] at hs ⊢
    omega

theorem forward_sentinel_clear (N : Nat) (q : Point) (hf : q ∈forward N) :
    q∉down ∧ q∉bottom N ∧ q∉firstVariable N := by
  have hs := forward_support N q hf
  have hl : 192≤q.2 := by
    dsimp [top] at hs
    rcases hs with hs | hs | hs | hs <;> omega
  refine ⟨?_,?_,?_⟩
  · intro h; have hb := down_support q h; omega
  · intro h; have hb := bottom_support N q h; omega
  · intro h; have hb := firstVariable_support N q h; omega

theorem returning_down_intersection (N : Nat) (q : Point)
    (hr : q ∈returning N) (hd : q ∈down) : q=sentinel N 0 := by
  have hr' := returning_bounds N q hr
  have hd' := down_support q hd
  apply Prod.ext <;> simp [sentinel] <;> omega

theorem returning_bottom_disjoint (N : Nat) : (returning N).Disjoint (bottom N) := by
  apply List.disjoint_left.mpr
  intro q hr hb
  have hr' := returning_bounds N q hr
  have hb' := bottom_support N q hb
  omega

theorem returning_firstVariable_disjoint (N : Nat) :
    (returning N).Disjoint (firstVariable N) := by
  apply List.disjoint_left.mpr
  intro q hr hf
  have hr' := returning_bounds N q hr
  have hf' := firstVariable_support N q hf
  dsimp [wireX] at hf'
  omega

/-- In the empty-formula case the closing link meets the variable strip
only at its starting endpoint. -/
theorem closing_variable_boundary (φ : Formula n 0) (hφ : Regular φ)
    (e : SatVariableDrawing.Edge n) (q : Point)
    (hc : q ∈closing) (hv : q ∈SatVariableDrawing.route φ e) :
    q=emptyExit 0 0 := by
  have hs := closing_support q hc
  have hb := SatVariableDrawing.route_bounds φ hφ e q hv
  dsimp [wireX] at hb
  rcases hs with hs | hs | hs | hs | hs
  · apply Prod.ext <;> dsimp [emptyExit,entryY,wireX] <;> omega
  all_goals omega

theorem closing_down_intersection (q : Point) (hc : q ∈closing) (hd : q ∈down) :
    q=sentinel 0 0 := by
  have hs := closing_support q hc
  have hb := down_support q hd
  have hy : q.2=0 := by
    rcases hs with hs | hs | hs | hs | hs <;> omega
  apply Prod.ext <;> simp [sentinel] <;> omega

theorem closing_bottom_disjoint : closing.Disjoint (bottom 0) := by
  apply List.disjoint_left.mpr
  intro q hc hb
  have hs := closing_support q hc
  have hb' := bottom_support 0 q hb
  rcases hs with hs | hs | hs | hs | hs <;> omega

theorem closing_firstVariable_disjoint : closing.Disjoint (firstVariable 0) := by
  apply List.disjoint_left.mpr
  intro q hc hf
  have hs := closing_support q hc
  have hf' := firstVariable_support 0 q hf
  dsimp [wireX] at hf'
  rcases hs with hs | hs | hs | hs | hs <;> omega

end GridHardness.SatExteriorSeparation
