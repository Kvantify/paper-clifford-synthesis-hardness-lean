/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatCrossover

/-!
# Planar SAT Crossover Routes Finite

Finite adjacency and incoming-edge computations for the crossover graph.
-/

@[expose] public section

namespace GridHardness.PlanarSatCrossover

def leftOut : Fin 5 → Option Vertex :=
  ![none, some (row 0 true), some (row 1 true), some (row 2 true), some (row 3 true)]

def rightOut : Fin 5 → Option Vertex :=
  ![some (row 0 true), some (row 1 true), some (row 2 true), some (row 3 true), none]

def neighbors : Vertex → List Vertex
  | .inl i => ![[h 1], [row 1 false], [h 1, h 3], [row 3 false],
      [row 0 false], [h 4, h 6], [row 2 false], [h 6]] i
  | .inr (.inl (i, false)) => [x i.castSucc 4, x i.succ 3]
  | .inr (.inl (i, true)) => [h (crossTarget i)]
  | .inr (.inr (i, j)) =>
      ![[x i 1] ++ (leftOut i).toList, [x i 5], [x i 1, x i 3], [x i 7],
        [x i 0], [x i 4, x i 6], [x i 2], [x i 6] ++ (rightOut i).toList] j

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem adj_iff_neighbors : ∀ u v, Adj u v ↔ v ∈ neighbors u := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
theorem h1_incoming : ∀ u, Adj u (h 1) ↔ u = h 0 ∨ u = h 2 := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
theorem h6_incoming : ∀ u, Adj u (h 6) ↔ u = h 5 ∨ u = h 7 := by decide

abbrev Rails := Fin 4 → Bool

def leftRails : Rails := ![false, true, true, true]
def rightRails : Rails := ![true, false, false, false]
def rails (left : Bool) : Rails := if left then leftRails else rightRails

/-- Internal successor; `none` denotes leaving the crossover. Four Boolean
choices are retained until the closed-component argument classifies them. -/
def candidate (b : Rails) (top : Bool) : Vertex → Option Vertex
  | .inl i =>
      ![if b 0 then some (h 1) else none, some (row 1 false),
        some (if b 1 then h 1 else h 3), some (row 3 false),
        some (row 0 false), some (if b 2 then h 4 else h 6),
        some (row 2 false), if b 3 then some (h 6) else none] i
  | .inr (.inl (i, false)) => some (if top then x i.succ 3 else x i.castSucc 4)
  | .inr (.inl (i, true)) => some (h (crossTarget i))
  | .inr (.inr (i, j)) =>
      if top then
        ![leftOut i, some (x i 5), some (x i 1), some (x i 7),
          some (x i 0), some (x i 4), some (x i 2), some (x i 6)] j
      else
        ![some (x i 1), some (x i 5), some (x i 3), some (x i 7),
          some (x i 0), some (x i 6), some (x i 2), rightOut i] j

def RailDegree (b : Rails) : Prop := b 0 ≠ b 1 ∧ b 3 = b 2
instance (b : Rails) : Decidable (RailDegree b) := inferInstanceAs (Decidable (_ ∧ _))

/-- Vertices which fail to leave within 56 steps. In a valid but unintended
rail pattern these include a closed component, not merely an incomplete route. -/
def trapped (b : Rails) (top : Bool) : Finset Vertex :=
  Finset.univ.filter (fun u => ((fun w => w.bind (candidate b top))^[56]) (some u) ≠ none)

def ClosedTrap (b : Rails) (top : Bool) : Prop :=
  ∀ u ∈ trapped b top, (candidate b top u).any (fun v => decide (v ∈ trapped b top)) = true
instance (b : Rails) (top : Bool) : Decidable (ClosedTrap b top) := by
  unfold ClosedTrap
  infer_instance

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option synthInstance.maxSize 2048 in
theorem candidate_classification : ∀ (b : Rails) (top : Bool), RailDegree b →
    b = leftRails ∨ b = rightRails ∨
      ((trapped b top).Nonempty ∧ verticalEntry top ∉ trapped b top ∧ ClosedTrap b top) := by
  decide

def pathLinks (left top : Bool) : List (Vertex × Vertex) :=
  (horizontalPath left top).zip (horizontalPath left top).tail ++
    (verticalPath top).zip (verticalPath top).tail

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option synthInstance.maxSize 2048 in
theorem classified_candidate : ∀ left top : Bool,
    (horizontalPath left top).IsChain (fun u v => candidate (rails left) top u = some v) ∧
    (verticalPath top).IsChain (fun u v => candidate (rails left) top u = some v) ∧
    (∀ u v, candidate (rails left) top u = some v ↔ (u, v) ∈ pathLinks left top) ∧
    (∀ u, candidate (rails left) top u = none ↔
      u = horizontalExit left ∨ u = verticalExit top) ∧
    (∀ v, (∀ u, candidate (rails left) top u ≠ some v) ↔
      v = horizontalEntry left ∨ v = verticalEntry top) := by
  decide

end GridHardness.PlanarSatCrossover
