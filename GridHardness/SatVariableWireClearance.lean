/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableLattice
public import GridHardness.SatClauseWireSeparation

/-!
# SAT Variable Wire Clearance

Variable-body routes meet the complete wire envelope only at their
designated true ports. The proof derives the boundary bands from the actual
wire route families, rather than assuming a completed drawing.
-/

public section

namespace GridHardness.SatVariableWireClearance
open CliffordSynthesis PermutationWireLayout SatVariableLattice
open SatClauseWireSeparation SatCrossingRetirement
set_option autoImplicit false

abbrev Point := Int × Int

variable {N : Nat} (p : Equiv.Perm (Fin N))

private theorem left_lt_wireX (last : Option (Fin N)) : Placement.left last<wireX N := by
  cases last with
  | none => dsimp [Placement.left,wireX]; omega
  | some i =>
    have hi := low_bounds i
    dsimp [Placement.left,wireX]
    omega

private theorem whole_boundary_band (last : Option (Fin N)) (i : Fin N)
    (hl : Placement.LastBefore last i) (r : Fin 4) (q : Point)
    (hq : q ∈Placement.route p last i r) (hx : q.1 =wireX N) :
    512*low i-4≤q.2 ∧ q.2≤512*low i+4 := by
  have hm := (Segments.whole_mem p last i hl r q).mp hq
  have hi := low_bounds i
  have ho := offset_bounds r
  dsimp [SatCrossingRouting.lane,wireX] at hm hx
  rcases hm with hm | hm | hm <;> omega

private theorem retired_boundary_band (i : Fin N) (v : Fin 8)
    (hx : (SatCrossingWireVertices.retired p i v).1 =wireX N) :
    512*low i-4≤(SatCrossingWireVertices.retired p i v).2 ∧
      (SatCrossingWireVertices.retired p i v).2≤512*low i+4 := by
  obtain ⟨r,hr⟩ := vertex_split v
  have hl := Catalogue.last_before p i
  have ho := offset_bounds r
  rcases hr with rfl | rfl
  · simp only [SatCrossingWireVertices.retired,Placement.true_coordinates p _ i hl]
    omega
  · have hb := left_lt_wireX (Catalogue.lastRequest? p i)
    simp only [SatCrossingWireVertices.retired,Placement.false_coordinates p _ i hl] at hx
    omega

/-- At the right boundary, the entire wire envelope lies within four
vertical steps of one of the actual occurrence heights. Cell interiors,
horizontal connectors, and vertical connectors lie strictly to its left. -/
theorem wire_boundary_band (q : Point) (hq : WirePoint p q) (hx : q.1 =wireX N) :
    ∃ i : Fin N, 512*low i-4≤q.2 ∧ q.2≤512*low i+4 := by
  cases hq with
  | cell c e q h =>
    have hb := SatCrossingLattice.coordinates_bounded p c q
      (SatCrossingLattice.route_in_box p c e q h)
    dsimp [wireX] at hx
    omega
  | vertical i j k r ho q h =>
    have hb := SatCrossingRouting.route_coordinates_bounded p i j k ho r q h
    dsimp [wireX] at hx
    omega
  | horizontal i k j ho q h =>
    have hb := SatCrossingHorizontal.route_coordinates_bounded p i k j ho q h
    dsimp [wireX] at hx
    omega
  | residual v q h =>
    have hl := Segments.lastInRow_before p _ v.1 (Residual.rowEnd_valid p v.1)
    exact ⟨v.1,whole_boundary_band p _ v.1 hl v.2.1 q
      (Residual.path_subset p _ v.1 hl v.2.1 v.2.2 h) hx⟩
  | side i e q h =>
    have hs := Sides.route_segments p i e q h
    rcases hs with hs | hs
    · exact ⟨i,hs.2⟩
    · have hb := left_lt_wireX (Residual.rowEnd p i)
      omega
  | vertex v =>
    cases v with
    | inl iv => exact ⟨iv.1,retired_boundary_band p iv.1 iv.2 hx⟩
    | inr cv =>
      have hb := SatCrossingLattice.coordinates_bounded p cv.1.val _
        (SatCrossingLattice.point_in_box p cv.1.val cv.2.val)
      change (SatCrossingLattice.point p cv.1.val cv.2.val).1=wireX N at hx
      dsimp [wireX] at hx
      omega

theorem entry_intersection (a : Nat) (_ha : a <N) (q : Point)
    (hq : q ∈entryRoute N a) (hw : WirePoint p q) : q=input N a := by
  have hb := wire_bounds p q hw
  have hr := entryRoute_bounds N a q hq
  have hx : q.1=wireX N := by dsimp [wireX] at hr ⊢; omega
  obtain ⟨i,hi⟩ := wire_boundary_band p q hw hx
  apply Prod.ext
  · exact hx
  · dsimp [input,entryY,low] at hr hi ⊢
    omega

theorem exit_intersection (b : Nat) (hb : 0 <b) (_hbN : b ≤N) (q : Point)
    (hq : q ∈exitRoute N b) (hw : WirePoint p q) : q=output N (b-1) := by
  have hw' := wire_bounds p q hw
  have hr := exitRoute_bounds N b q hq
  have hx : q.1=wireX N := by dsimp [wireX] at hr ⊢; omega
  obtain ⟨i,hi⟩ := wire_boundary_band p q hw hx
  apply Prod.ext
  · exact hx
  · dsimp [output,exitY,low] at hr hi ⊢
    omega

theorem between_intersection (i : Nat) (q : Point)
    (hq : q ∈betweenRoute N i) (hw : WirePoint p q) :
    q=output N i ∨ q=input N (i+1) := by
  have hr := (SatCrossingRouting.rising_mem _ _ _ q).mp hq
  obtain ⟨j,hj⟩ := wire_boundary_band p q hw hr.1
  have hy : q.2=512*((i:Int)+1)+4 ∨ q.2=512*((i:Int)+2)-4 := by
    dsimp [low] at hj
    omega
  rcases hy with hy | hy
  · left
    apply Prod.ext
    · exact hr.1
    · exact hy
  · right
    apply Prod.ext
    · exact hr.1
    · dsimp [input]
      omega

/-- Every point on the exterior vertical body line has a quantitative
gap from every wire route, including all retained wire vertices. -/
theorem exterior_separation (q r : Point) (hq : q.1 =wireX N +64)
    (hr : WirePoint p r) : 64≤IntegerGrid.manhattan q r := by
  have hb := wire_bounds p r hr
  dsimp [wireX,IntegerGrid.manhattan] at hq ⊢
  omega

theorem direct_separation (a b : Nat) (q r : Point)
    (hq : q ∈directRoute N a b) (hr : WirePoint p r) :
    64≤IntegerGrid.manhattan q r :=
  exterior_separation p q r ((SatCrossingRouting.rising_mem _ _ _ q).mp hq).1 hr

theorem backbone_separation (b : Nat) (q r : Point)
    (hq : q ∈backboneRoute N b) (hr : WirePoint p r) :
    64≤IntegerGrid.manhattan q r :=
  exterior_separation p q r ((SatCrossingRouting.rising_mem _ _ _ q).mp hq).1 hr

theorem empty_separation (a : Nat) (q r : Point)
    (hq : q ∈emptyRoute N a) (hr : WirePoint p r) :
    64≤IntegerGrid.manhattan q r :=
  exterior_separation p q r ((SatCrossingRouting.rising_mem _ _ _ q).mp hq).1 hr

theorem direct_clear (a b : Nat) (q : Point) (hq : q ∈directRoute N a b) :
    ¬WirePoint p q := by
  intro hw
  have hs := direct_separation p a b q q hq hw
  simp [IntegerGrid.manhattan] at hs

theorem backbone_clear (b : Nat) (q : Point) (hq : q ∈backboneRoute N b) :
    ¬WirePoint p q := by
  intro hw
  have hs := backbone_separation p b q q hq hw
  simp [IntegerGrid.manhattan] at hs

theorem empty_clear (a : Nat) (q : Point) (hq : q ∈emptyRoute N a) :
    ¬WirePoint p q := by
  intro hw
  have hs := empty_separation p a q q hq hw
  simp [IntegerGrid.manhattan] at hs

end GridHardness.SatVariableWireClearance
