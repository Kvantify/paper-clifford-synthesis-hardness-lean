/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseWireLattice
public import GridHardness.SatCrossingHorizontalSeparation
public import GridHardness.SatExteriorSeparation
public import GridHardness.SatVariableChainDrawing

/-!
# SAT Clause Wire Connector Clearance

Clause links stop before the first active cell of their row. Consequently
they stay clear of all horizontal and vertical inter-cell connectors. The
proofs use the actual inversion condition and first-request minimality.
-/

public section

namespace GridHardness.SatClauseWireConnectorClearance
open CliffordSynthesis PermutationWireLayout SatCrossingRouting
open SatClauseWireLattice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev Point := Int × Int

variable {N : Nat} (p : Equiv.Perm (Fin N))

/-- Every active cell in a row lies to the right of that row's clause link. -/
theorem finishX_le_active (i j : Fin N) (h : Active p i j) :
    finishX p j ≤ 512 * low i - 65 := by
  cases hf : firstRequest? p j with
  | none => exact False.elim ((firstRequest_none p j).mp hf i h)
  | some a =>
    have ha := (firstRequest_sound p a j hf).2 i h
    have hl : low a ≤ low i := by dsimp [low]; omega
    simpa only [finishX, hf] using
      (by omega : 512 * low a - 65 ≤ 512 * low i - 65)

/-- A clause link is separated from every horizontal inter-cell connection,
including the connection in its own row. -/
theorem horizontal_separation (j i k l : Fin N) (b side : Bool)
    (hc : SatCrossingHorizontal.ConsecutiveColumns p i k l)
    (q r : Point) (hq : q ∈ SatClauseWireLattice.route p j b)
    (hr : r ∈ SatCrossingHorizontal.connectionRoute p i k l side) :
    110 ≤ IntegerGrid.manhattan q r := by
  have hq' := (SatClauseWireLattice.route_mem p j b q).mp hq
  have hr' := SatCrossingHorizontal.route_bounds p i k l hc.2.2.1 r
    (SatCrossingHorizontal.connectionRoute_mem p i k l side r hr)
  dsimp [IntegerGrid.manhattan]
  by_cases hj : j = l
  · subst l
    have hx := finishX_le_active p i j hc.1
    omega
  · have hh : high p j ≠ high p l := fun he => hj (high_injective p he)
    cases b <;> dsimp [height] at hq' <;> omega

/-- A clause link is separated from every vertical inter-cell connection.
If a vertical lane reached its horizontal extent, that lane would supply an
earlier active request, contradicting the selected first crossing. -/
theorem vertical_separation (j i a k : Fin N) (b : Bool) (lane : Fin 4)
    (hc : Consecutive p i a k) (q r : Point)
    (hq : q ∈ SatClauseWireLattice.route p j b)
    (hr : r ∈ SatCrossingRouting.route p i a k lane) :
    20 ≤ IntegerGrid.manhattan q r := by
  have hq' := (SatClauseWireLattice.route_mem p j b q).mp hq
  have hr' := (SatCrossingRouting.route_mem p i a k hc.2.2.1 lane r).mp hr
  have hl := lane.isLt
  dsimp [IntegerGrid.manhattan]
  cases hf : firstRequest? p j with
  | none =>
    have hx : q.1 ≤ 0 := by simpa [finishX, hf] using hq'.2.2
    have hi := low_bounds i
    dsimp [SatCrossingRouting.lane] at hr'
    omega
  | some f =>
    have hfj := firstRequest_sound p f j hf
    have hx : q.1 ≤ 512 * low f - 65 := by
      simpa [finishX, hf] using hq'.2.2
    by_cases hfi : f ≤ i
    · have hlow : low f ≤ low i := by dsimp [low]; omega
      dsimp [SatCrossingRouting.lane] at hr'
      omega
    · have hij : i < j := lt_trans (lt_of_not_ge hfi) hfj.1.1
      have hp : p k < p j := by
        by_contra hn
        have hactive : Active p i j := ⟨hij, lt_of_le_of_lt (le_of_not_gt hn) hc.2.1.2⟩
        exact hfi (hfj.2 i hactive)
      have hh := (high_lt_high p).mpr hp
      cases b <;> dsimp [height] at hq' <;> omega

theorem horizontal_clear (j i k l : Fin N) (b side : Bool)
    (hc : SatCrossingHorizontal.ConsecutiveColumns p i k l)
    (q : Point) (hq : q ∈ SatClauseWireLattice.route p j b) :
    q ∉ SatCrossingHorizontal.connectionRoute p i k l side := by
  intro hr
  have h := horizontal_separation p j i k l b side hc q q hq hr
  simp [IntegerGrid.manhattan] at h

theorem vertical_clear (j i a k : Fin N) (b : Bool) (lane : Fin 4)
    (hc : Consecutive p i a k)
    (q : Point) (hq : q ∈ SatClauseWireLattice.route p j b) :
    q ∉ SatCrossingRouting.route p i a k lane := by
  intro hr
  have h := vertical_separation p j i a k b lane hc q q hq hr
  simp [IntegerGrid.manhattan] at h

variable {n m : Nat}

/-- The left boundary point of a clause link is its literal vertex. -/
theorem clause_endpoint_of_x (φ : PlanarSatAssembly.Formula n m)
    (o : PlanarSatAssembly.Occurrence m) (b : Bool) (q : Point)
    (hq : q ∈ SatClauseWireLattice.route (SatClauseOrder.permutation φ)
      (SatWireLayout.variableRank φ o) b) (hx : q.1 = -64) :
    q = SatClauseOrder.point o.1
      (if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2) := by
  have hr := (SatClauseWireLattice.route_mem _ _ _ q).mp hq
  have he : q = clausePoint (SatClauseOrder.permutation φ)
      (SatWireLayout.variableRank φ o) b := by
    exact Prod.ext hx hr.1
  exact he.trans (clause_endpoint φ o b)

/-- A clause link meets a clause-backbone route only at a shared clause
vertex. The two alternatives identify the source and target of that route. -/
theorem clause_backbone_intersection (φ : PlanarSatAssembly.Formula n m)
    (o : PlanarSatAssembly.Occurrence m) (b : Bool)
    (c d : Fin m) (hcd : d.val = c.val + 1) (q : Point)
    (hq : q ∈ SatClauseWireLattice.route (SatClauseOrder.permutation φ)
      (SatWireLayout.variableRank φ o) b)
    (hr : q ∈ SatClauseBackbone.route c) :
    (o.1 = c ∧ q = SatClauseOrder.point c 1 ∧
      (if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2) = 1) ∨
    (o.1 = d ∧ q = SatClauseOrder.point d 8 ∧
      (if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2) = 8) := by
  have hx := (SatClauseBackbone.route_mem c q).mp hr
  have he := clause_endpoint_of_x φ o b q hq hx.1
  have hb : SatClauseOrder.InBox o.1 q := he.symm ▸
    SatClauseOrder.point_in_box o.1
      (if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2)
  rcases SatClauseBackbone.box_intersection c d o.1 hcd q hr hb with hc | hd
  · have hv := SatClauseOrder.point_injective m
      (a₁ := (o.1,if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2))
      (a₂ := (c,1)) (he.symm.trans hc.2)
    exact Or.inl ⟨hc.1, hc.2, congrArg Prod.snd hv⟩
  · have hv := SatClauseOrder.point_injective m
      (a₁ := (o.1,if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2))
      (a₂ := (d,8)) (he.symm.trans hd.2)
    exact Or.inr ⟨hd.1, hd.2, congrArg Prod.snd hv⟩

theorem variable_body_separation (φ : PlanarSatAssembly.Formula n m)
    (hφ : SatVariablePlacement.Regular φ) (j : Fin (3 *m)) (b : Bool)
    (e : SatVariableDrawing.Edge n) (q r : Point)
    (hq : q ∈ SatClauseWireLattice.route (SatClauseOrder.permutation φ) j b)
    (hr : r ∈ SatVariableDrawing.route φ e) :
    706 ≤ IntegerGrid.manhattan q r := by
  have hq' := SatClauseWireLattice.route_bounds _ j b q hq
  have hr' := SatVariableDrawing.route_bounds φ hφ e r hr
  dsimp [SatVariableLattice.wireX, IntegerGrid.manhattan] at hr' ⊢
  omega

theorem variable_chain_separation (φ : PlanarSatAssembly.Formula n m)
    (j : Fin (3 *m)) (b : Bool) (e : SatVariableChainDrawing.Edge φ) (q r : Point)
    (hq : q ∈ SatClauseWireLattice.route (SatClauseOrder.permutation φ) j b)
    (hr : r ∈ SatVariableChainDrawing.route e) :
    642 ≤ IntegerGrid.manhattan q r := by
  have hq' := SatClauseWireLattice.route_bounds _ j b q hq
  have hr' := SatVariableChainDrawing.route_bounds e r hr
  dsimp [SatVariableLattice.wireX, IntegerGrid.manhattan] at hr' ⊢
  omega

theorem down_separation (j : Fin N) (b : Bool) (q r : Point)
    (hq : q ∈ SatClauseWireLattice.route p j b) (hr : r ∈ SatExteriorLattice.down) :
    64 ≤ IntegerGrid.manhattan q r := by
  have hq' := (SatClauseWireLattice.route_mem p j b q).mp hq
  have hr' := SatExteriorSeparation.down_support r hr
  dsimp [IntegerGrid.manhattan]
  omega

theorem bottom_separation (j : Fin N) (b : Bool) (q r : Point)
    (hq : q ∈ SatClauseWireLattice.route p j b) (hr : r ∈ SatExteriorLattice.bottom N) :
    64 ≤ IntegerGrid.manhattan q r := by
  have hq' := SatClauseWireLattice.route_bounds p j b q hq
  have hr' := SatExteriorSeparation.bottom_support N r hr
  dsimp [IntegerGrid.manhattan]
  omega

theorem first_variable_separation (j : Fin N) (b : Bool) (q r : Point)
    (hq : q ∈ SatClauseWireLattice.route p j b)
    (hr : r ∈ SatExteriorLattice.firstVariable N) :
    706 ≤ IntegerGrid.manhattan q r := by
  have hq' := SatClauseWireLattice.route_bounds p j b q hq
  have hr' := SatExteriorSeparation.firstVariable_support N r hr
  dsimp [SatVariableLattice.wireX, IntegerGrid.manhattan] at hr' ⊢
  omega

/-- The forward exterior link can meet a clause link only at the entry
vertex of the first clause. -/
theorem forward_intersection (φ : PlanarSatAssembly.Formula n m)
    (o : PlanarSatAssembly.Occurrence m) (b : Bool) (q : Point)
    (hq : q ∈ SatClauseWireLattice.route (SatClauseOrder.permutation φ)
      (SatWireLayout.variableRank φ o) b)
    (hr : q ∈ SatExteriorLattice.forward (3 *m)) :
    o.1.val = 0 ∧ q = SatClauseOrder.point o.1 8 ∧
      (if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2) = 8 := by
  have hq' := SatClauseWireLattice.route_bounds _ _ b q hq
  have hs := SatExteriorLattice.forward_support (3*m) q hr
  have hx : q.1 = -64 := by
    dsimp [SatVariableLattice.wireX, SatExteriorLattice.top] at hs
    rcases hs with h | h | h | h <;> omega
  have he := clause_endpoint_of_x φ o b q hq hx
  have hb : SatClauseOrder.InBox o.1 q := he.symm ▸
    SatClauseOrder.point_in_box o.1
      (if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2)
  have h := SatExteriorLattice.forward_clause_intersection o.1 q hr hb
  have hv := SatClauseOrder.point_injective m
    (a₁ := (o.1,if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2))
    (a₂ := (o.1,8)) (he.symm.trans h.2)
  exact ⟨h.1, h.2, congrArg Prod.snd hv⟩

/-- The returning exterior link can meet a clause link only at the exit
vertex of the final clause. -/
theorem returning_intersection (φ : PlanarSatAssembly.Formula n m)
    (o : PlanarSatAssembly.Occurrence m) (b : Bool) (q : Point)
    (hq : q ∈ SatClauseWireLattice.route (SatClauseOrder.permutation φ)
      (SatWireLayout.variableRank φ o) b)
    (hr : q ∈ SatExteriorLattice.returning (3 *m)) :
    o.1.val + 1 = m ∧ q = SatClauseOrder.point o.1 1 ∧
      (if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2) = 1 := by
  have hq' := (SatClauseWireLattice.route_mem _ _ b q).mp hq
  have hy := high_bounds (SatClauseOrder.permutation φ) (SatWireLayout.variableRank φ o)
  have hs := SatExteriorLattice.returning_support (3*m) q hr
  have hx : q.1 = -64 := by
    rcases hs with h | h
    · exact h.1
    · cases b <;> dsimp [height] at hq' <;> omega
  have he := clause_endpoint_of_x φ o b q hq hx
  have hb : SatClauseOrder.InBox o.1 q := he.symm ▸
    SatClauseOrder.point_in_box o.1
      (if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2)
  have h := SatExteriorLattice.returning_clause_intersection o.1 q hr hb
  have hv := SatClauseOrder.point_injective m
    (a₁ := (o.1,if b then PlanarSatAssembly.clauseTop o.2 else PlanarSatAssembly.clauseBottom o.2))
    (a₂ := (o.1,1)) (he.symm.trans h.2)
  exact ⟨h.1, h.2, congrArg Prod.snd hv⟩

end GridHardness.SatClauseWireConnectorClearance
