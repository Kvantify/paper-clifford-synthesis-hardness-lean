/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatCrossoverGraph
public import GridProblems.Geometry

/-!
# Crossover Lattice

An explicit orthogonal lattice drawing of the complete crossover.
The main XOR rails occupy the two vertical sides of a 20 by 130 rectangle.
Five alternately mirrored XOR ladders occupy its middle strip. Every edge
is a straight segment or a two-segment orthogonal route. The checks below
certify the actual 80-arc graph, not a schematic or assumed embedding.
-/

@[expose] public section

namespace GridHardness.PlanarSatCrossover.Lattice

abbrev Point := Int × Int

local instance (l m : List Point) : Decidable (l.Disjoint m) :=
  inferInstanceAs (Decidable (∀ p ∈ l, p ∉ m))

def point : Vertex → Point
  | Sum.inl j => (if j.val < 4 then 0 else 20, 20 + 30 * (j.val % 4))
  | Sum.inr (Sum.inl (i, out)) =>
    (if i.val % 2 = 0 then (if out then 4 else 16) else (if out then 16 else 4),
      20 + 30 * i.val)
  | Sum.inr (Sum.inr (i, j)) =>
    let a : Int := ![14, 12, 8, 6] ⟨j.val % 4, Nat.mod_lt _ (by decide)⟩
    (if i.val % 2 = 0 then a else 20 - a, 30 * i.val + if j.val < 4 then 0 else 10)

def edge (i : Fin 80) : Vertex × Vertex :=
  edges.get ⟨i.val, by rw [edges_length]; exact i.isLt⟩

/-- Inclusive unit-step list for an axis-parallel segment. -/
def segment (a b : Point) : List Point :=
  if a.2 = b.2 then
    (List.range ((b.1 - a.1).natAbs + 1)).map
      (fun k => (a.1 + (b.1 - a.1).sign * k, a.2))
  else
    (List.range ((b.2 - a.2).natAbs + 1)).map
      (fun k => (a.1, a.2 + (b.2 - a.2).sign * k))

def bend (u v : Vertex) : Point :=
  match u with
  | Sum.inr (Sum.inl (_, false)) => ((point u).1, (point v).2)
  | _ => ((point v).1, (point u).2)

def edgeRoute (i : Fin 80) : List Point :=
  let u := (edge i).1
  let v := (edge i).2
  segment (point u) (bend u v) ++ (segment (bend u v) (point v)).tail

def interior (i : Fin 80) : List Point := (edgeRoute i).tail.dropLast

def UnitStep (a b : Point) : Prop := CliffordSynthesis.IntegerGrid.manhattan a b = 1
instance : DecidableRel UnitStep := fun _ _ => inferInstanceAs (Decidable (_ = _))

def InBox (p : Point) : Prop := 0 ≤ p.1 ∧ p.1 ≤ 20 ∧ 0 ≤ p.2 ∧ p.2 ≤ 130
instance (p : Point) : Decidable (InBox p) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation enumerates the finite grid crossover and its routes.
theorem point_injective : Function.Injective point := by decide

-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation enumerates the finite grid crossover and its routes.
theorem edge_injective : Function.Injective edge := by decide

theorem edge_adj (e : Fin 80) : Adj (edge e).1 (edge e).2 := by
  exact List.get_mem _ _

theorem adj_iff_edge (u v : Vertex) : Adj u v ↔ ∃ e : Fin 80, edge e = (u, v) := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    exact ⟨⟨i.val, by simpa only [edges_length] using i.isLt⟩, hi⟩
  · rintro ⟨e, he⟩
    simpa only [he] using edge_adj e

-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option synthInstance.maxSize 2048 in
theorem route_certificate : ∀ e : Fin 80,
    (edgeRoute e).head? = some (point (edge e).1) ∧
    (edgeRoute e).getLast? = some (point (edge e).2) ∧
    (edgeRoute e).Nodup ∧ (edgeRoute e).IsChain UnitStep ∧
    2 ≤ (edgeRoute e).length ∧ (edgeRoute e).length ≤ 31 ∧
    ∀ p ∈ edgeRoute e, InBox p := by decide

-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option synthInstance.maxSize 2048 in
theorem route_vertex_clear : ∀ (e : Fin 80) (v : Vertex),
    point v ∈ edgeRoute e ↔ v = (edge e).1 ∨ v = (edge e).2 := by decide

-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option synthInstance.maxSize 2048 in
theorem interiors_disjoint : ∀ e f : Fin 80, e ≠ f →
    (interior e).Disjoint (edgeRoute f) := by decide

-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation enumerates the finite grid crossover and its routes.
theorem intersection_certificate : ∀ e f : Fin 80, e ≠ f →
    ∀ p ∈ edgeRoute e, p ∈ edgeRoute f →
      (p = point (edge e).1 ∨ p = point (edge e).2) ∧
      (p = point (edge f).1 ∨ p = point (edge f).2) := by decide

/-- The four boundary pairs alternate around the rectangle: top channel,
right channel, bottom channel, left channel. Directions agree with Figure 8. -/
theorem port_coordinates :
    point (verticalEntry true) = (6, 0) ∧ point (verticalExit true) = (14, 0) ∧
    point (horizontalEntry false) = (20, 20) ∧ point (horizontalExit false) = (20, 110) ∧
    point (verticalEntry false) = (14, 130) ∧ point (verticalExit false) = (6, 130) ∧
    point (horizontalEntry true) = (0, 110) ∧ point (horizontalExit true) = (0, 20) := by decide

-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation enumerates the finite grid crossover and its routes.
set_option synthInstance.maxSize 2048 in
theorem boundary_vertices : ∀ v : Vertex,
    ((point v).1 = 0 ∨ (point v).1 = 20 ∨ (point v).2 = 0 ∨ (point v).2 = 130) ↔
      v ∈ entries ∨ v ∈ exits ∨ v = h 1 ∨ v = h 2 ∨ v = h 5 ∨ v = h 6 ∨
      v = x 0 1 ∨ v = x 0 2 ∨ v = x 4 5 ∨ v = x 4 6 := by decide

end GridHardness.PlanarSatCrossover.Lattice
