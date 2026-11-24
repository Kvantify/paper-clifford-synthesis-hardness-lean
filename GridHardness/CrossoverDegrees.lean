/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatCrossoverRoutesFinite

/-!
# Crossover Degrees

Degree bounds for the actual crossover adjacency. Every boundary port
has one internal predecessor and one internal successor; all other vertices
have total degree three, split as one incoming/two outgoing or conversely.
-/

@[expose] public section

namespace GridHardness.PlanarSatCrossover

def inDegree (v : Vertex) : Nat := (Finset.univ.filter (fun u => Adj u v)).card
def outDegree (v : Vertex) : Nat := (Finset.univ.filter (fun u => Adj v u)).card

-- Kernel evaluation enumerates the vertices and arcs of the crossover gadget.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation enumerates the vertices and arcs of the crossover gadget.
theorem degree_bounds : ∀ v : Vertex,
    inDegree v ≤ 2 ∧ outDegree v ≤ 2 ∧ inDegree v + outDegree v ≤ 3 := by
  simp only [inDegree, outDegree, adj_iff_neighbors]
  decide

-- Kernel evaluation enumerates the vertices and arcs of the crossover gadget.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation enumerates the vertices and arcs of the crossover gadget.
theorem port_degrees : ∀ v : Vertex, v ∈ entries ∨ v ∈ exits →
    inDegree v = 1 ∧ outDegree v = 1 := by
  simp only [inDegree, outDegree, adj_iff_neighbors]
  decide

-- Kernel evaluation enumerates the vertices and arcs of the crossover gadget.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation enumerates the vertices and arcs of the crossover gadget.
theorem nonport_degree_three : ∀ v : Vertex, v ∉ entries → v ∉ exits →
    inDegree v + outDegree v = 3 := by
  simp only [inDegree, outDegree, adj_iff_neighbors]
  decide

end GridHardness.PlanarSatCrossover
