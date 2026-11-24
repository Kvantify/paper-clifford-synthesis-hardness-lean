/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseBackbone
public import GridHardness.SatCrossingRetirementSides

/-!
# SAT Clause Wire Separation

The clause bodies and their consecutive-clause links are separated
from every already constructed wire route. The wire envelope deliberately
includes all local cell routes, so this result does not require identifying
which cell edges survive the sweep. It is a geometric clearance theorem,
not a claim that the full graph has been drawn.
-/

public section

namespace GridHardness.SatClauseWireSeparation
open CliffordSynthesis PlanarSatAssembly
set_option autoImplicit false

abbrev Point := Int × Int

/-- An overapproximation by explicit route families, with only order
conditions needed to define the connectors. -/
inductive WirePoint {n : Nat} (p : Equiv.Perm (Fin n)) : Point → Prop where
  | cell (c : SatCrossingLattice.Cell n) (e : Fin 66) (q : Point)
      (mem : q∈SatCrossingLattice.route p c e) : WirePoint p q
  | vertical (i j k : Fin n) (r : Fin 4) (order : p j<p k) (q : Point)
      (mem : q∈SatCrossingRouting.route p i j k r) : WirePoint p q
  | horizontal (i k j : Fin n) (order : i<k) (q : Point)
      (mem : q∈SatCrossingHorizontal.upperRoute p i k j ∨
        q∈SatCrossingHorizontal.lowerRoute p i k j) : WirePoint p q
  | residual (v : SatCrossingRetirement.Residual.Index p) (q : Point)
      (mem : q∈SatCrossingRetirement.Residual.route p v) : WirePoint p q
  | side (i : Fin n) (e : Fin 6) (q : Point)
      (mem : q∈SatCrossingRetirement.Sides.route p i e) : WirePoint p q
  | vertex (v : SatCrossingWireVertices.Vertex p) :
      WirePoint p (SatCrossingWireVertices.point p v)

theorem wire_bounds {n : Nat} (p : Equiv.Perm (Fin n)) (q : Point)
    (hq : WirePoint p q) :
    0≤q.1 ∧ q.1≤512*(n+1)+65 ∧ 0≤q.2 ∧ q.2≤1024*n+522 := by
  cases hq with
  | cell c e q h =>
    have hb := SatCrossingLattice.coordinates_bounded p c q
      (SatCrossingLattice.route_in_box p c e q h)
    omega
  | vertical i j k r horder q h =>
    have hb := SatCrossingRouting.route_coordinates_bounded p i j k horder r q h
    omega
  | horizontal i k j horder q h =>
    have hb := SatCrossingHorizontal.route_coordinates_bounded p i k j horder q h
    omega
  | residual v q h =>
    have hb := SatCrossingRetirement.Residual.route_bounds p v q h
    omega
  | side i e q h =>
    have hb := SatCrossingRetirement.Sides.route_bounds p i e q h
    omega
  | vertex v =>
    have hb := SatCrossingWireVertices.point_bounds p v
    omega

/-- Quantitative clearance applies to entire clause boxes, not merely to
their twelve vertices. It also excludes unintended unit-grid edges. -/
theorem box_separation {n m : Nat} (φ : Formula n m) (c : Fin m) (q r : Point)
    (hq : SatClauseOrder.InBox c q) (hr : WirePoint (SatClauseOrder.permutation φ) r) :
    64≤IntegerGrid.manhattan q r := by
  have hb := wire_bounds _ r hr
  change -104≤q.1 ∧ q.1≤-64 ∧ _ at hq
  dsimp [IntegerGrid.manhattan]
  omega

theorem internal_route_separation {n m : Nat} (φ : Formula n m)
    (c : Fin m) (e : Fin 14) (q r : Point)
    (hq : q ∈SatClauseOrder.route c e) (hr : WirePoint (SatClauseOrder.permutation φ) r) :
    64≤IntegerGrid.manhattan q r :=
  box_separation φ c q r (SatClauseOrder.route_in_box c e q hq) hr

theorem backbone_separation {n m : Nat} (φ : Formula n m) (c : Fin m) (q r : Point)
    (hq : q ∈SatClauseBackbone.route c) (hr : WirePoint (SatClauseOrder.permutation φ) r) :
    64≤IntegerGrid.manhattan q r := by
  have hb := wire_bounds _ r hr
  have hx := (SatClauseBackbone.route_mem c q).mp hq
  dsimp [SatClauseBackbone.OnRoute,IntegerGrid.manhattan] at hx ⊢
  omega

theorem internal_route_clear {n m : Nat} (φ : Formula n m)
    (c : Fin m) (e : Fin 14) (q : Point) (hq : q ∈SatClauseOrder.route c e) :
    ¬WirePoint (SatClauseOrder.permutation φ) q := by
  intro h
  have hs := internal_route_separation φ c e q q hq h
  simp [IntegerGrid.manhattan] at hs

theorem backbone_clear {n m : Nat} (φ : Formula n m)
    (c : Fin m) (q : Point) (hq : q ∈SatClauseBackbone.route c) :
    ¬WirePoint (SatClauseOrder.permutation φ) q := by
  intro h
  have hs := backbone_separation φ c q q hq h
  simp [IntegerGrid.manhattan] at hs

end GridHardness.SatClauseWireSeparation
