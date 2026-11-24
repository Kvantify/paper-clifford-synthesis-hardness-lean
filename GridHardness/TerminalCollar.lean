/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.TwoClusterAssembly

/-!
# Terminal Collar

A bounded terminal detour changes an eastbound corridor into the
single-edge port of an odd nine-cluster. The incoming straight portion
has arbitrary length; the four additional strips have fixed lengths.
-/

@[expose] public section

namespace GridHardness.TerminalCollar
open CliffordSynthesis OrthogonalTentacle SignedTentacle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

def incomingFrame (n : Nat) : Frame := ⟨true, false, false, (-8 - (n : Int), 0)⟩
def northFrame : Frame := ⟨false, false, false, (-8, 0)⟩
def upperFrame : Frame := ⟨true, false, false, (-8, 3)⟩
def southFrame : Frame := ⟨false, true, false, (-5, 4)⟩
def terminalFrame : Frame := ⟨true, false, true, (-5, -1)⟩

def first (n : Nat) : Drawing := .attach (.base (incomingFrame n) n) northFrame 3
def second (n : Nat) : Drawing := .attach (first n) upperFrame 3
def third (n : Nat) : Drawing := .attach (second n) southFrame 5
def drawing (n : Nat) : Drawing := .attach (third n) terminalFrame 4

theorem mem_incoming (n : Nat) (p : Point) : p ∈ strip (incomingFrame n) n ↔
    -8 - (n : Int) ≤ p.1 ∧ p.1 ≤ -8 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  simp only [mem_strip_iff, incomingFrame, Frame.unmap, sign, ite_true,
    Bool.false_eq_true, ite_false, sub_zero]
  omega

theorem mem_north (p : Point) : p ∈ strip northFrame 3 ↔
    -8 ≤ p.1 ∧ p.1 ≤ -7 ∧ 0 ≤ p.2 ∧ p.2 ≤ 3 := by
  simp only [mem_strip_iff, northFrame, Frame.unmap, sign, Bool.false_eq_true,
    ite_false, sub_zero]
  omega

theorem mem_upper (p : Point) : p ∈ strip upperFrame 3 ↔
    -8 ≤ p.1 ∧ p.1 ≤ -5 ∧ 3 ≤ p.2 ∧ p.2 ≤ 4 := by
  simp only [mem_strip_iff, upperFrame, Frame.unmap, sign, ite_true,
    Bool.false_eq_true, ite_false]
  omega

theorem mem_south (p : Point) : p ∈ strip southFrame 5 ↔
    -5 ≤ p.1 ∧ p.1 ≤ -4 ∧ -1 ≤ p.2 ∧ p.2 ≤ 4 := by
  simp only [mem_strip_iff, southFrame, Frame.unmap, sign, ite_true,
    Bool.false_eq_true, ite_false]
  omega

theorem mem_terminal (p : Point) : p ∈ strip terminalFrame 4 ↔
    -5 ≤ p.1 ∧ p.1 ≤ -1 ∧ -2 ≤ p.2 ∧ p.2 ≤ -1 := by
  simp only [mem_strip_iff, terminalFrame, Frame.unmap, sign, ite_true,
    Bool.false_eq_true, ite_false]
  omega

theorem first_overlap (n : Nat) :
    strip (incomingFrame n) n ∩ strip northFrame 3 =
      {join northFrame 0, join northFrame 1} := by
  ext ⟨x,y⟩
  simp only [Finset.mem_inter, mem_incoming, mem_north, Finset.mem_insert,
    Finset.mem_singleton]
  simp only [join, northFrame, Frame.map, place, sign, Bool.false_eq_true, ite_false,
    Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one, add_zero, Prod.mk.injEq]
  omega

theorem first_separated (n : Nat) :
    Separated (strip (incomingFrame n) n) (strip northFrame 3) := by
  intro p hp q hq ha
  rw [mem_incoming] at hp
  rw [mem_north] at hq
  change IntegerGrid.manhattan p q = 1 at ha
  rw [manhattan_one_iff] at ha
  rw [mem_north, mem_incoming]
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  simp only [Prod.mk.injEq] at ha
  dsimp at hp hq ⊢
  omega

theorem first_valid (n : Nat) (hn : 3 ≤ n) : (first n).Valid := by
  refine ⟨hn, by decide, ?_, first_overlap n, first_separated n⟩
  left
  constructor <;> simp [Drawing.tip, incomingFrame, northFrame, SignedTentacle.far, join,
    Frame.map, place, sign]

theorem second_overlap (n : Nat) :
    (first n).points ∩ strip upperFrame 3 = {join upperFrame 0, join upperFrame 1} := by
  ext ⟨x,y⟩
  simp only [first, Drawing.points, Finset.mem_inter, Finset.mem_union,
    mem_incoming, mem_north, mem_upper, Finset.mem_insert, Finset.mem_singleton]
  simp only [join, upperFrame, Frame.map, place, sign, Bool.false_eq_true, ite_false,
    ite_true, Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    add_zero, Prod.mk.injEq]
  omega

theorem second_separated (n : Nat) : Separated (first n).points (strip upperFrame 3) := by
  intro p hp q hq ha
  change p ∈ strip (incomingFrame n) n ∪ strip northFrame 3 at hp
  rw [Finset.mem_union, mem_incoming, mem_north] at hp
  rw [mem_upper] at hq
  change IntegerGrid.manhattan p q = 1 at ha
  rw [manhattan_one_iff] at ha
  change p ∈ strip upperFrame 3 ∨ q ∈ strip (incomingFrame n) n ∪ strip northFrame 3
  rw [mem_upper, Finset.mem_union, mem_incoming, mem_north]
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  simp only [Prod.mk.injEq] at ha
  dsimp at hp hq ⊢
  omega

theorem second_valid (n : Nat) (hn : 3 ≤ n) : (second n).Valid := by
  refine ⟨first_valid n hn, by decide, ?_, second_overlap n, second_separated n⟩
  left
  constructor <;> rfl

theorem third_overlap (n : Nat) :
    (second n).points ∩ strip southFrame 5 = {join southFrame 0, join southFrame 1} := by
  ext ⟨x,y⟩
  simp only [second, first, Drawing.points, Finset.mem_inter, Finset.mem_union,
    mem_incoming, mem_north, mem_upper, mem_south, Finset.mem_insert, Finset.mem_singleton]
  simp only [join, southFrame, Frame.map, place, sign, Bool.false_eq_true, ite_false,
    ite_true, Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    neg_zero, add_zero, Prod.mk.injEq]
  omega

theorem third_separated (n : Nat) : Separated (second n).points (strip southFrame 5) := by
  intro p hp q hq ha
  simp only [second, first, Drawing.points, Finset.mem_union,
    mem_incoming, mem_north, mem_upper] at hp
  rw [mem_south] at hq
  change IntegerGrid.manhattan p q = 1 at ha
  rw [manhattan_one_iff] at ha
  simp only [second, first, Drawing.points, Finset.mem_union,
    mem_incoming, mem_north, mem_upper, mem_south]
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  simp only [Prod.mk.injEq] at ha
  dsimp at hp hq ⊢
  omega

theorem third_valid (n : Nat) (hn : 3 ≤ n) : (third n).Valid := by
  refine ⟨second_valid n hn, by decide, ?_, third_overlap n, third_separated n⟩
  right
  constructor <;> rfl

theorem terminal_overlap (n : Nat) :
    (third n).points ∩ strip terminalFrame 4 = {join terminalFrame 0, join terminalFrame 1} := by
  ext ⟨x,y⟩
  simp only [third, second, first, Drawing.points, Finset.mem_inter, Finset.mem_union,
    mem_incoming, mem_north, mem_upper, mem_south, mem_terminal,
    Finset.mem_insert, Finset.mem_singleton]
  simp only [join, terminalFrame, Frame.map, place, sign, Bool.false_eq_true, ite_false,
    ite_true, Fin.val_zero, Fin.val_one, Int.natCast_zero, Int.natCast_one,
    neg_zero, add_zero, Prod.mk.injEq]
  omega

theorem terminal_separated (n : Nat) : Separated (third n).points (strip terminalFrame 4) := by
  intro p hp q hq ha
  simp only [third, second, first, Drawing.points, Finset.mem_union,
    mem_incoming, mem_north, mem_upper, mem_south] at hp
  rw [mem_terminal] at hq
  change IntegerGrid.manhattan p q = 1 at ha
  rw [manhattan_one_iff] at ha
  simp only [third, second, first, Drawing.points, Finset.mem_union,
    mem_incoming, mem_north, mem_upper, mem_south, mem_terminal]
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  simp only [Prod.mk.injEq] at ha
  dsimp at hp hq ⊢
  omega

/-- Every incoming straight length at least three admits this fixed
four-turn terminal collar, with all induced edges checked geometrically. -/
theorem drawing_valid (n : Nat) (hn : 3 ≤ n) : (drawing n).Valid := by
  refine ⟨third_valid n hn, by decide, ?_, terminal_overlap n, terminal_separated n⟩
  left
  constructor <;> rfl

theorem start_coordinates (n : Nat) (r : Fin 2) :
    (drawing n).start r = (-8 - (n : Int), (r.val : Int)) := by
  simp [drawing, third, second, first, Drawing.start, incomingFrame, near,
    Frame.map, place, sign]

theorem tip_coordinates (n : Nat) (r : Fin 2) :
    (drawing n).tip r = (-1, -1 - (r.val : Int)) := by
  simp [drawing, Drawing.tip, terminalFrame, SignedTentacle.far, Frame.map, place, sign, sub_eq_add_neg]

theorem drawing_bounds (n : Nat) {p : Point} (hp : p ∈ (drawing n).points) :
    -8 - (n : Int) ≤ p.1 ∧ p.1 ≤ -1 ∧ -2 ≤ p.2 ∧ p.2 ≤ 4 := by
  simp only [drawing, third, second, first, Drawing.points, Finset.mem_union,
    mem_incoming, mem_north, mem_upper, mem_south, mem_terminal] at hp
  omega

theorem drawing_card (n : Nat) (hn : 3 ≤ n) :
    (drawing n).points.card = 2 * (n + 16) := by
  rw [Drawing.card _ (drawing_valid n hn)]
  simp only [drawing, third, second, first, Drawing.halfSize]

/-- The odd target cluster is centered one lattice unit right of the
original route endpoint, so its lower-left corner has odd parity. -/
def clusterFrame : Frame := ⟨true, false, false, (0, -1)⟩

theorem mem_cluster (p : Point) : p ∈ TwoClusterAssembly.cluster clusterFrame ↔
    0 ≤ p.1 ∧ p.1 ≤ 2 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1 := by
  simp only [TwoClusterAssembly.mem_cluster_iff, clusterFrame, Frame.unmap,
    sign, ite_true, Bool.false_eq_true, ite_false, sub_zero]
  omega

theorem cluster_disjoint (n : Nat) :
    Disjoint (TwoClusterAssembly.cluster clusterFrame) (drawing n).points := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hc := (mem_cluster p).mp hp
  have hd := drawing_bounds n hq
  omega

/-- The full bent collar, including its arbitrary incoming portion, has
exactly one lattice edge to the target cluster, at terminal lane zero. -/
theorem cluster_boundary (n : Nat) {c t : Point}
    (hc : c ∈ TwoClusterAssembly.cluster clusterFrame) (ht : t ∈ (drawing n).points) :
    lattice.Adj c t ↔ c = TwoClusterAssembly.corner clusterFrame 0 ∧ t = (drawing n).tip 0 := by
  have hc' := (mem_cluster c).mp hc
  simp only [drawing, third, second, first, Drawing.points, Finset.mem_union,
    mem_incoming, mem_north, mem_upper, mem_south, mem_terminal] at ht
  change IntegerGrid.manhattan c t = 1 ↔ _
  rw [manhattan_one_iff, tip_coordinates]
  rcases c with ⟨x,y⟩
  rcases t with ⟨u,v⟩
  simp only [TwoClusterAssembly.corner, clusterFrame, Frame.map,
    NineClusterAttachment.corner, NineCluster.point, NineCluster.port,
    place, sign, ite_true, Bool.false_eq_true, ite_false, Matrix.cons_val_zero,
    Fin.val_zero, Int.natCast_zero, Prod.mk.injEq]
  dsimp at hc' ht ⊢
  omega

theorem boundary_singleton (n : Nat) (hn : 3 ≤ n) :
    TwoClusterAssembly.boundary (TwoClusterAssembly.cluster clusterFrame) (drawing n).points =
      {(TwoClusterAssembly.corner clusterFrame 0, (drawing n).tip 0)} := by
  exact TwoClusterAssembly.boundary_eq_singleton
    (TwoClusterAssembly.corner_mem clusterFrame 0)
    ((drawing n).tip_mem (drawing_valid n hn) 0)
    (fun _ hc _ ht => cluster_boundary n hc ht)

/-- The fixed geometric part of the collar, including its joining rung. -/
def collarPoints : Finset Point :=
  strip northFrame 3 ∪ strip upperFrame 3 ∪ strip southFrame 5 ∪ strip terminalFrame 4

theorem collar_card : collarPoints.card = 32 := by decide

theorem collar_bounds {p : Point} (hp : p ∈ collarPoints) :
    -8 ≤ p.1 ∧ p.1 ≤ -1 ∧ -2 ≤ p.2 ∧ p.2 ≤ 4 := by
  simp only [collarPoints, Finset.mem_union, mem_north, mem_upper, mem_south,
    mem_terminal] at hp
  omega

theorem points_union (n : Nat) :
    (drawing n).points = strip (incomingFrame n) n ∪ collarPoints := by
  simp only [drawing, third, second, first, Drawing.points, collarPoints, Finset.union_assoc]

/-- Only the incoming terminal rung lies in the fixed collar. -/
theorem incoming_collar_overlap (n : Nat) :
    strip (incomingFrame n) n ∩ collarPoints = {(-8,0),(-8,1)} := by
  ext ⟨x,y⟩
  simp only [collarPoints, Finset.mem_inter, Finset.mem_union, mem_incoming,
    mem_north, mem_upper, mem_south, mem_terminal, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  omega

/-- The detour contributes exactly thirty new lattice vertices,
independently of the incoming straight length. -/
theorem fresh_card (n : Nat) :
    (collarPoints \ strip (incomingFrame n) n).card = 30 := by
  have hi := incoming_collar_overlap n
  have hcard : (collarPoints ∩ strip (incomingFrame n) n).card = 2 := by
    rw [Finset.inter_comm, hi]
    decide
  have hc := Finset.card_sdiff_add_card_inter collarPoints (strip (incomingFrame n) n)
  rw [hcard, collar_card] at hc
  omega

end GridHardness.TerminalCollar
