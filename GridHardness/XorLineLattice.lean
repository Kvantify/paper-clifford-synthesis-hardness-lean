/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLinePorts
public import GridHardness.CrossoverLattice

/-!
# XOR Line Lattice

An explicit orthogonal lattice drawing of the XOR-line
refinement across four mandatory arcs. Its 48 vertices and all 66 directed
arcs are checked below. Original Boolean endpoint pairs stay together at the
top and bottom; each mandatory row has its own input/output boundary pair.
This finite local drawing makes no claim about a global SAT placement.
-/

@[expose] public section

namespace GridHardness.XorLine.Lattice
set_option synthInstance.maxSize 2048

abbrev Point := Int × Int

local instance (l m : List Point) : Decidable (l.Disjoint m) :=
  inferInstanceAs (Decidable (∀ p ∈ l, p ∉ m))

local instance : BEq (Vertex 4) := instBEqOfDecidableEq
local instance : LawfulBEq (Vertex 4) := by infer_instance
local instance (v : Vertex 4) : Decidable (IsInput 4 v) := by
  cases v <;> dsimp [IsInput] <;> infer_instance
local instance (v : Vertex 4) : Decidable (IsOutput 4 v) := by
  cases v <;> dsimp [IsOutput] <;> infer_instance

/-- Five alternately mirrored XORs, with the four row pairs on the sides. -/
def point : Vertex 4 → Point
  | .inl (i,j) =>
    let a : Int := ![14,12,8,6] ⟨j.val % 4,Nat.mod_lt _ (by decide)⟩
    (if i.val % 2 = 0 then a else 20-a,30*i.val + if j.val < 4 then 0 else 10)
  | .inr (i,b) =>
    (if i.val % 2 = 0 then (if b then 0 else 20) else (if b then 20 else 0),
      20+30*i.val)

/-- Enumerate the actual local graph, without selecting a route or truth value. -/
def edges : List (Vertex 4 × Vertex 4) :=
  (List.finRange 5).flatMap (fun i => (List.finRange 10).map (fun e =>
    (x i (XorGadget.arc e).1,x i (XorGadget.arc e).2))) ++
  (List.finRange 4).flatMap (fun i =>
    [(row i false,x i.castSucc 4),(row i false,x i.succ 3),
      (x i.castSucc 7,row i true),(x i.succ 0,row i true)])

theorem vertex_card : Fintype.card (Vertex 4) = 48 := by decide
theorem edges_length : edges.length = 66 := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem mem_edges_iff : ∀ u v : Vertex 4, (u,v) ∈ edges ↔ Adj 4 u v := by decide

def edge (i : Fin 66) : Vertex 4 × Vertex 4 :=
  edges.get ⟨i.val,by rw [edges_length]; exact i.isLt⟩

abbrev segment := PlanarSatCrossover.Lattice.segment

def bend (u v : Vertex 4) : Point :=
  match u with
  | .inr (_,false) => ((point u).1,(point v).2)
  | _ => ((point v).1,(point u).2)

def edgeRoute (i : Fin 66) : List Point :=
  let u := (edge i).1
  let v := (edge i).2
  segment (point u) (bend u v) ++ (segment (bend u v) (point v)).tail

def interior (i : Fin 66) : List Point := (edgeRoute i).tail.dropLast

abbrev UnitStep := PlanarSatCrossover.Lattice.UnitStep
abbrev InBox := PlanarSatCrossover.Lattice.InBox

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem point_injective : Function.Injective point := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem edge_injective : Function.Injective edge := by decide

theorem edge_adj (i : Fin 66) : Adj 4 (edge i).1 (edge i).2 :=
  (mem_edges_iff _ _).mp (List.get_mem _ _)

theorem adj_iff_edge (u v : Vertex 4) : Adj 4 u v ↔ ∃ i : Fin 66, edge i = (u,v) := by
  rw [← mem_edges_iff]
  constructor
  · intro h
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp h
    exact ⟨⟨i.val,by simpa only [edges_length] using i.isLt⟩,hi⟩
  · rintro ⟨i,he⟩
    exact he ▸ List.get_mem edges ⟨i.val,by rw [edges_length]; exact i.isLt⟩

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option synthInstance.maxSize 2048 in
theorem route_certificate : ∀ i : Fin 66,
    (edgeRoute i).head? = some (point (edge i).1) ∧
    (edgeRoute i).getLast? = some (point (edge i).2) ∧
    (edgeRoute i).Nodup ∧ (edgeRoute i).IsChain UnitStep ∧
    2 ≤ (edgeRoute i).length ∧ (edgeRoute i).length ≤ 17 ∧
    ∀ p ∈ edgeRoute i, InBox p := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem route_vertex_clear : ∀ (i : Fin 66) (v : Vertex 4),
    point v ∈ edgeRoute i ↔ v = (edge i).1 ∨ v = (edge i).2 := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option synthInstance.maxSize 2048 in
theorem interiors_disjoint : ∀ i j : Fin 66, i ≠ j →
    (interior i).Disjoint (edgeRoute j) := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem intersection_certificate : ∀ i j : Fin 66, i ≠ j →
    ∀ p ∈ edgeRoute i, p ∈ edgeRoute j →
      (p = point (edge i).1 ∨ p = point (edge i).2) ∧
      (p = point (edge j).1 ∨ p = point (edge j).2) := by decide

/-- The two original XOR endpoint pairs lie together on opposite boundaries. -/
theorem main_port_coordinates :
    point (inputPort 4 (.inl true)) = (6,0) ∧
    point (outputPort 4 (.inl true)) = (14,0) ∧
    point (inputPort 4 (.inl false)) = (14,130) ∧
    point (outputPort 4 (.inl false)) = (6,130) := by decide

/-- Each mandatory row has independent opposite-side input/output ports,
alternating its direction between consecutive rows. -/
theorem row_port_coordinates : ∀ i : Fin 4,
    point (inputPort 4 (.inr i)) =
      (if i.val % 2 = 0 then 20 else 0,20+30*(i.val : Int)) ∧
    point (outputPort 4 (.inr i)) =
      (if i.val % 2 = 0 then 0 else 20,20+30*(i.val : Int)) := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem boundary_vertices : ∀ v : Vertex 4,
    ((point v).1 = 0 ∨ (point v).1 = 20 ∨ (point v).2 = 0 ∨ (point v).2 = 130) ↔
      IsInput 4 v ∨ IsOutput 4 v ∨ v=x 0 1 ∨ v=x 0 2 ∨ v=x 4 5 ∨ v=x 4 6 := by decide

end GridHardness.XorLine.Lattice
