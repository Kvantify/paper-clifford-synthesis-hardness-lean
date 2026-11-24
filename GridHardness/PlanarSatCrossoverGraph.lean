/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatXor

/-!
# Planar SAT Crossover Graph

The actual 56-vertex XOR-line crossover of Bosboom et al. (2020),
Figure 8. Four cross-edges of a horizontal XOR are split into parallel
branches, coupled by five vertical XOR gadgets. There are eight boundary
ports and no extra assumptions about truth assignments in the graph.

`horizontalPath` and `verticalPath` give four explicit disjoint path
covers, one for each pair of signal values. Exhaustiveness of these covers
is not proved here. The graph has 80 directed edges.
-/

@[expose] public section

namespace GridHardness.PlanarSatCrossover

abbrev Vertex := Fin 8 ⊕ ((Fin 4 × Bool) ⊕ (Fin 5 × Fin 8))
instance : BEq Vertex := instBEqOfDecidableEq
instance : LawfulBEq Vertex := by infer_instance

def h (i : Fin 8) : Vertex := Sum.inl i
def row (i : Fin 4) (out : Bool) : Vertex := Sum.inr (Sum.inl (i, out))
def x (i : Fin 5) (j : Fin 8) : Vertex := Sum.inr (Sum.inr (i, j))

def crossSource : Fin 4 → Fin 8 := ![4, 1, 6, 3]
def crossTarget : Fin 4 → Fin 8 := ![0, 5, 2, 7]

def edges : List (Vertex × Vertex) :=
  [(h 0, h 1), (h 2, h 1), (h 2, h 3), (h 5, h 4), (h 5, h 6), (h 7, h 6)] ++
  (List.finRange 4).flatMap (fun i =>
    [(h (crossSource i), row i false), (row i true, h (crossTarget i)),
      (row i false, x i.castSucc 4), (x i.castSucc 7, row i true),
      (row i false, x i.succ 3), (x i.succ 0, row i true)]) ++
  (List.finRange 5).flatMap (fun i => (List.finRange 10).map (fun e =>
    (x i (XorGadget.arc e).1, x i (XorGadget.arc e).2)))

def Adj (u v : Vertex) : Prop := (u, v) ∈ edges
instance : DecidableRel Adj := by
  letI : BEq (Vertex × Vertex) := instBEqOfDecidableEq
  exact fun u v => inferInstanceAs (Decidable ((u, v) ∈ edges))

def entries : List Vertex := [h 3, h 4, x 0 3, x 4 4]
def exits : List Vertex := [h 0, h 7, x 0 0, x 4 7]

def horizontalEntry (left : Bool) : Vertex := if left then h 3 else h 4
def horizontalExit (left : Bool) : Vertex := if left then h 0 else h 7
def verticalEntry (top : Bool) : Vertex := if top then x 0 3 else x 4 4
def verticalExit (top : Bool) : Vertex := if top then x 0 0 else x 4 7

def rowPath (top : Bool) (i : Fin 4) : List Vertex :=
  [row i false] ++
    (if top then XorGadget.leftVertices.map (x i.succ)
      else XorGadget.rightVertices.map (x i.castSucc)) ++ [row i true]

def horizontalNode (top : Bool) (v : Fin 8) : List Vertex :=
  [h v] ++ (if v = 4 then rowPath top 0 else
    if v = 1 then rowPath top 1 else
    if v = 6 then rowPath top 2 else
    if v = 3 then rowPath top 3 else [])

def horizontalPath (left top : Bool) : List Vertex :=
  (if left then XorGadget.leftVertices else XorGadget.rightVertices).flatMap (horizontalNode top)

def verticalPath (top : Bool) : List Vertex :=
  if top then XorGadget.leftVertices.map (x 0) else XorGadget.rightVertices.map (x 4)

theorem vertex_card : Fintype.card Vertex = 56 := by decide
theorem edges_length : edges.length = 80 := by decide

-- Kernel evaluation checks the finite SAT crossover graph.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite SAT crossover graph.
set_option synthInstance.maxSize 2048 in
theorem path_certificate : ∀ left top : Bool,
    (horizontalPath left top).IsChain Adj ∧ (verticalPath top).IsChain Adj ∧
    (horizontalPath left top).head? = some (horizontalEntry left) ∧
    (horizontalPath left top).getLast? = some (horizontalExit left) ∧
    (verticalPath top).head? = some (verticalEntry top) ∧
    (verticalPath top).getLast? = some (verticalExit top) ∧
    (horizontalPath left top).length = 48 ∧ (verticalPath top).length = 8 ∧
    ∀ v : Vertex, (horizontalPath left top).count v + (verticalPath top).count v = 1 := by
  decide

theorem x_injective (i : Fin 5) : Function.Injective (x i) := by
  intro u v he
  simpa [x] using he

-- Kernel evaluation checks the finite SAT crossover graph.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite SAT crossover graph.
theorem x_outgoing : ∀ (i : Fin 5) (j : Fin 8), j ≠ 0 → j ≠ 7 →
    ∀ v, Adj (x i j) v ↔
      ∃ e : Fin 10, (XorGadget.arc e).1 = j ∧ v = x i (XorGadget.arc e).2 := by
  decide

-- Kernel evaluation checks the finite SAT crossover graph.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite SAT crossover graph.
theorem x_incoming : ∀ (i : Fin 5) (j : Fin 8), j ≠ 3 → j ≠ 4 →
    ∀ v, Adj v (x i j) ↔
      ∃ e : Fin 10, (XorGadget.arc e).2 = j ∧ v = x i (XorGadget.arc e).1 := by
  decide

-- Kernel evaluation checks the finite SAT crossover graph.
set_option maxRecDepth 65536 in
theorem x_nonexit : ∀ (i : Fin 5) (j : Fin 8), j ≠ 0 → j ≠ 7 → x i j ∉ exits := by decide

-- Kernel evaluation checks the finite SAT crossover graph.
set_option maxRecDepth 65536 in
theorem x_nonentry : ∀ (i : Fin 5) (j : Fin 8), j ≠ 3 → j ≠ 4 → x i j ∉ entries := by decide

-- Kernel evaluation checks the finite SAT crossover graph.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite SAT crossover graph.
theorem row_outgoing : ∀ (i : Fin 4) (v : Vertex),
    Adj (row i false) v ↔ v = x i.castSucc 4 ∨ v = x i.succ 3 := by decide

-- Kernel evaluation checks the finite SAT crossover graph.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite SAT crossover graph.
theorem upper_entry_incoming : ∀ (i : Fin 4) (v : Vertex),
    Adj v (x i.castSucc 4) ↔ v = x i.castSucc 5 ∨ v = row i false := by decide

-- Kernel evaluation checks the finite SAT crossover graph.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite SAT crossover graph.
theorem lower_entry_incoming : ∀ (i : Fin 4) (v : Vertex),
    Adj v (x i.succ 3) ↔ v = x i.succ 2 ∨ v = row i false := by decide

end GridHardness.PlanarSatCrossover
