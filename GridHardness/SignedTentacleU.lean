/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SignedTentacle

/-!
# Signed Tentacle U

A genuine non-monotone family of valid signed tentacles: travel east,
turn north, then turn west. All three lengths are arbitrary numbers ≥3;
separation and overlap are proved from coordinate inequalities.
-/

@[expose] public section

namespace GridHardness.SignedTentacle
open CliffordSynthesis SimpleGraph SimpleGraph.Walk OrthogonalTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def eastFrame : Frame := ⟨true, false, false, (0, 0)⟩
def northFrame (a : Nat) : Frame := ⟨false, false, false, (a, 0)⟩
def westFrame (a b : Nat) : Frame := ⟨true, true, false, ((a : Int) + 1, b)⟩

theorem mem_east (a : Nat) (p : Point) : p ∈ strip eastFrame a ↔
    0 ≤ p.1 ∧ p.1 ≤ a ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  simp [mem_strip_iff, eastFrame, Frame.unmap, sign]

theorem mem_north (a b : Nat) (p : Point) : p ∈ strip (northFrame a) b ↔
    (a : Int) ≤ p.1 ∧ p.1 ≤ (a : Int) + 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ b := by
  simp only [mem_strip_iff, northFrame, Frame.unmap, sign, Bool.false_eq_true, ite_false,
    sub_zero]
  omega

theorem mem_west (a b c : Nat) (p : Point) : p ∈ strip (westFrame a b) c ↔
    (a : Int) + 1 - c ≤ p.1 ∧ p.1 ≤ (a : Int) + 1 ∧ (b : Int) ≤ p.2 ∧ p.2 ≤ (b : Int) + 1 := by
  simp only [mem_strip_iff, westFrame, Frame.unmap, sign, ite_true, Bool.false_eq_true, ite_false]
  omega

def lTurn (a b : Nat) : Drawing := .attach (.base eastFrame a) (northFrame a) b
def uTurn (a b c : Nat) : Drawing := .attach (lTurn a b) (westFrame a b) c

theorem east_north_overlap (a b : Nat) (hb : 1 ≤ b) :
    strip eastFrame a ∩ strip (northFrame a) b = {join (northFrame a) 0, join (northFrame a) 1} := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [Finset.mem_inter, mem_east, mem_north, Finset.mem_insert, Finset.mem_singleton]
  simp only [join, northFrame, Frame.map, place, sign, Bool.false_eq_true, ite_false, Fin.val_zero,
    Fin.val_one, Int.natCast_zero, Int.natCast_one, add_zero, Prod.mk.injEq]
  omega

theorem east_north_separated (a b : Nat) : Separated (strip eastFrame a) (strip (northFrame a) b) := by
  intro p hp q hq ha
  rw [mem_east] at hp
  rw [mem_north] at hq
  change IntegerGrid.manhattan p q = 1 at ha
  rw [manhattan_one_iff] at ha
  rw [mem_north, mem_east]
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  simp only [Prod.mk.injEq] at ha
  dsimp at hp hq ⊢
  omega

theorem lTurn_valid (a b : Nat) (ha : 3 ≤ a) (hb : 3 ≤ b) : (lTurn a b).Valid := by
  refine ⟨ha, hb, ?_, east_north_overlap a b (by omega), east_north_separated a b⟩
  left
  constructor <;> simp [Drawing.tip, eastFrame, northFrame, far, join, Frame.map, place, sign]

theorem lTurn_west_overlap (a b c : Nat) (hb : 3 ≤ b) (hc : 1 ≤ c) :
    (lTurn a b).points ∩ strip (westFrame a b) c = {join (westFrame a b) 0, join (westFrame a b) 1} := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [lTurn, Drawing.points, Finset.mem_inter, Finset.mem_union, mem_east, mem_north,
    mem_west, Finset.mem_insert, Finset.mem_singleton]
  simp only [join, westFrame, Frame.map, place,
    sign, ite_true, Bool.false_eq_true, ite_false, Fin.val_zero, Fin.val_one,
    Int.natCast_zero, Int.natCast_one, neg_zero, add_zero, Prod.mk.injEq]
  omega

theorem lTurn_west_separated (a b c : Nat) (hb : 3 ≤ b) :
    Separated (lTurn a b).points (strip (westFrame a b) c) := by
  intro p hp q hq ha
  change p ∈ strip eastFrame a ∪ strip (northFrame a) b at hp
  rw [Finset.mem_union, mem_east, mem_north] at hp
  rw [mem_west] at hq
  change IntegerGrid.manhattan p q = 1 at ha
  rw [manhattan_one_iff] at ha
  change p ∈ strip (westFrame a b) c ∨ q ∈ strip eastFrame a ∪ strip (northFrame a) b
  rw [mem_west, Finset.mem_union, mem_east, mem_north]
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  simp only [Prod.mk.injEq] at ha
  dsimp at hp hq ⊢
  omega

/-- Every triple of lengths ≥3 gives a valid east–north–west chain. No
separation, routing, or Hamiltonicity assumptions remain in this theorem. -/
theorem uTurn_valid (a b c : Nat) (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) :
    (uTurn a b c).Valid := by
  refine ⟨lTurn_valid a b ha hb, hc, ?_, lTurn_west_overlap a b c hb (by omega),
    lTurn_west_separated a b c hb⟩
  right
  constructor <;> apply Prod.ext <;>
    simp [Drawing.tip, lTurn, northFrame, westFrame, far, join, Frame.map, place, sign]

/-- The final strip reverses the horizontal direction of the initial strip. -/
theorem uTurn_tip_coordinates (a b c : Nat) (r : Fin 2) :
    (uTurn a b c).tip r = ((a : Int) + 1 - c, (b : Int) + r.val) := by
  simp [uTurn, Drawing.tip, westFrame, far, Frame.map, place, sign, sub_eq_add_neg]

theorem uTurn_card (a b c : Nat) (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) :
    (uTurn a b c).points.card = 2 * (a + b + c + 1) := by
  rw [Drawing.card _ (uTurn_valid a b c ha hb hc)]
  simp only [uTurn, lTurn, Drawing.halfSize]
  omega

/-- Actual finite-grid cross Hamiltonian paths, including the parity
obstruction, for the non-monotone U family. -/
theorem uTurn_hamiltonian_iff (a b c : Nat) (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c)
    (r t : Fin 2) :
    (∃ p : (finiteGrid (uTurn a b c).points).Walk
      ⟨(uTurn a b c).start r, Drawing.start_mem _ (uTurn_valid a b c ha hb hc) r⟩
      ⟨(uTurn a b c).tip t, Drawing.tip_mem _ (uTurn_valid a b c ha hb hc) t⟩,
      p.IsHamiltonian) ↔ color ((uTurn a b c).start r) ≠ color ((uTurn a b c).tip t) :=
  Drawing.hamiltonian_iff _ (uTurn_valid a b c ha hb hc) r t

theorem uTurn_start_return_hamiltonian (a b c : Nat) (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) :
    ∃ p : (finiteGrid (uTurn a b c).points).Walk
      ⟨(uTurn a b c).start 0, Drawing.start_mem _ (uTurn_valid a b c ha hb hc) 0⟩
      ⟨(uTurn a b c).start 1, Drawing.start_mem _ (uTurn_valid a b c ha hb hc) 1⟩,
      p.IsHamiltonian := Drawing.start_return_hamiltonian _ (uTurn_valid a b c ha hb hc)

theorem uTurn_terminal_return_hamiltonian (a b c : Nat) (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) :
    ∃ p : (finiteGrid (uTurn a b c).points).Walk
      ⟨(uTurn a b c).tip 0, Drawing.tip_mem _ (uTurn_valid a b c ha hb hc) 0⟩
      ⟨(uTurn a b c).tip 1, Drawing.tip_mem _ (uTurn_valid a b c ha hb hc) 1⟩,
      p.IsHamiltonian := Drawing.terminal_return_hamiltonian _ (uTurn_valid a b c ha hb hc)

end GridHardness.SignedTentacle
