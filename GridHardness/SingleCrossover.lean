/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CrossoverReplacement
public import GridHardness.TwoXorReplacement

/-!
# Single Crossover

A complete graph-level replacement of two isolated XOR channels by
the 56-vertex crossover. Boundary connections to the rest of the graph are
unchanged, and both directions preserve a single global Hamiltonian cycle.

This graph replacement theorem takes one marked crossing as input and does
not assert a planar drawing. The replaced pair must have no additional
edges between its own vertices besides the two XOR gadgets' internal arcs.
-/

public section

namespace GridHardness

/-- Replace a pair of XORs inside any finite outside graph. The graph
construction contains no truth assignment; the proof extracts route choices
from a Hamiltonian cycle and transfers its exact endpoint wiring. -/
theorem single_crossover_correct {O : Type*} [Finite O]
    (outside : O → O → Prop)
    (enter : O → Bool → Bool → Prop) (leave : Bool → Bool → O → Prop) :
    PathCover.Hamiltonian (TwoXorGadget.attached outside enter leave) ↔
      PathCover.Hamiltonian (PlanarSatCrossover.attached outside enter leave) :=
  (TwoXorGadget.attached_hamiltonian_iff outside enter leave).trans
    (PlanarSatCrossover.attached_hamiltonian_iff outside enter leave).symm

end GridHardness
