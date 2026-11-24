/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GridAssemblyGeometry
public import GridHardness.SelectMarking
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Grid Assembly Encoding

Enumerate the coordinates of a finite grid assembly in lexicographic order
and reduce Hamiltonian cycle to Hamiltonian path on the resulting instance.
-/

@[expose] public section

namespace GridHardness.GridAssembly
open CliffordSynthesis SimpleGraph SimpleGraph.Walk OrthogonalTentacle SignedTentacle
open CliffordComplexity GridProblems GridProblems.GridCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

namespace Encoding

local instance : LinearOrder Point := Prod.Lex.instLinearOrder Int Int

/-- A computable ordering of the coordinate set; the only role of the order
is to give the graph's vertices distinct consecutive numbers. -/
def numbering (S : Finset Point) {n : Nat} (hn : S.card = n) : Fin n ≃ S :=
  (S.orderIsoOfFin hn).toEquiv

def pointList (S : Finset Point) : CycleInputTy.denote :=
  List.ofFn (fun i : Fin S.card => encodePoint (numbering S rfl i).val)

theorem pointList_eq {S : Finset Point} {n : Nat} (hn : S.card = n) :
    pointList S = List.ofFn (fun i : Fin n => encodePoint (numbering S hn i).val) := by
  subst n
  rfl

@[simp] theorem pointList_length (S : Finset Point) : (pointList S).length = S.card := by
  exact List.length_ofFn

@[simp] theorem decode_encode (p : Point) : decoded (encodePoint p) = p := by
  rcases p with ⟨x, y⟩
  simp [decoded, encodePoint]

theorem coordinates_injective {S : Finset Point} {n : Nat} (hn : S.card = n) :
    Function.Injective (decoded ∘ (fun i : Fin n => encodePoint (numbering S hn i).val)) := by
  intro i j he
  apply (numbering S hn).injective
  apply Subtype.ext
  simpa only [Function.comp_apply, decode_encode] using he

/-- The encoded source problem denotes exactly the induced finite grid,
including the nonempty-list convention of that source problem. -/
theorem pointList_correct (S : Finset Point) (hpos : 0 < S.card) :
    GRID_HAMILTONIAN_CYCLE (pointList S) ↔
      ∃ (v : S) (p : (finiteGrid S).Walk v v), p.IsHamiltonianCycle := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [pointList_eq hm, cycle_source_input]
  apply (and_iff_right (coordinates_injective hm)).trans
  apply exists_isHamiltonianCycle_iff_of_equiv (numbering S hm)
  intro a b
  change IntegerGrid.manhattan (decoded (encodePoint (numbering S hm a).val))
    (decoded (encodePoint (numbering S hm b).val)) = 1 ↔
      IntegerGrid.manhattan (numbering S hm a).val (numbering S hm b).val = 1
  simp only [decode_encode]

end Encoding

namespace Layout
variable {C : Type*} [Fintype C]

def cycleInput (l : Layout C) : CycleInputTy.denote := Encoding.pointList l.points

/-- Convert the assembly's cycle instance to a specified-endpoint path instance. -/
def pathInput (l : Layout C) : InputTy.denote := certifiedGridCycleToPath.code.eval l.cycleInput

namespace Valid
variable {l : Layout C} {H : SimpleGraph C} [DecidableRel H.Adj] (hv : l.Valid H)
include hv

theorem cycleInput_length : l.cycleInput.length =
    9 * Fintype.card C + 2 * ∑ c, (l.body c).halfTentacleSize := by
  rw [cycleInput, Encoding.pointList_length, hv.points_card]

/-- A geometric assembly defines an encoded grid-cycle instance to which the
certified cycle-to-path program applies. -/
theorem cycleInput_correct [DecidableEq C] (hc : 3 ≤ Fintype.card C)
    (hd : ∀ c, H.degree c ≤ 3) :
    (∃ (c : C) (p : H.Walk c c), p.IsHamiltonianCycle) ↔
      GRID_HAMILTONIAN_CYCLE l.cycleInput := by
  have hpos : 0 < l.points.card := by rw [hv.points_card]; omega
  exact (hv.hamiltonianCycle_iff hc hd).symm.trans
    (Encoding.pointList_correct l.points hpos).symm

/-- Hamiltonian cycles in the source graph correspond to the specified-endpoint grid paths. -/
theorem pathInput_correct [DecidableEq C] (hc : 3 ≤ Fintype.card C)
    (hd : ∀ c, H.degree c ≤ 3) :
    (∃ (c : C) (p : H.Walk c c), p.IsHamiltonianCycle) ↔
      GRID_HAMILTONIAN_PATH l.pathInput :=
  (hv.cycleInput_correct hc hd).trans (certifiedGridCycleToPath.correct l.cycleInput)

end Valid

end Layout
end GridHardness.GridAssembly
