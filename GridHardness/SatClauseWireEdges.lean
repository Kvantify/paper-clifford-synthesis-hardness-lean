/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalClauseEdges
public import GridHardness.SatClauseWireDrawing

/-!
# SAT Clause Wire Edges

The clause-link routes have exactly the graph endpoints established
by the full interval sweep, including the first-crossing convention.
-/

public section

namespace GridHardness.SatClauseWireDrawing
open PlanarSatAssembly CorrectedSatInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n m : Nat}

theorem actualWireVertex_eq_port (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    actualWireVertex φ o b=ClauseEdges.port φ (SatClauseOrder.permutation φ)
      (SatWireLayout.variableRank φ o) (!b) := by
  cases hf : SatClauseWireLattice.firstRequest? (SatClauseOrder.permutation φ)
      (SatWireLayout.variableRank φ o) with
  | none =>
    rw [actualWireVertex,wireVertex_none _ _ b hf,PermutationWirePlacement.vertex_original,
      ClauseEdges.port_none _ _ _ hf]
    cases b <;> rfl
  | some i =>
    rw [actualWireVertex,wireVertex_some _ _ _ b hf,PermutationWirePlacement.vertex_fresh,
      ClauseEdges.port_some _ _ _ _ hf]
    cases b <;> rfl

/-- Each geometric clause link is an actual directed edge of the final
graph, without any drawing or boundary-transport premise. -/
theorem edge_is_arc (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    (SatClauseOrder.graph φ).adj (source φ o b) (target φ o b) := by
  cases b
  · change (SatClauseOrder.graph φ).adj (clauseVertex φ o false) (actualWireVertex φ o false)
    rw [actualWireVertex_eq_port]
    exact ClauseEdges.incoming φ (SatClauseOrder.permutation φ) o
  · change (SatClauseOrder.graph φ).adj (actualWireVertex φ o true) (clauseVertex φ o true)
    rw [actualWireVertex_eq_port]
    exact ClauseEdges.outgoing φ (SatClauseOrder.permutation φ) o

theorem incoming_body_iff (φ : Formula n m) (o : Occurrence m)
    (v : PlanarSatAssembly.Vertex n m) (hv : CoreEdges.Body v) :
    (SatClauseOrder.graph φ).adj
      (PermutationGraph.liftOriginal φ (SatClauseOrder.permutation φ) v)
      (actualWireVertex φ o false) ↔ v=clause o.1 (clauseBottom o.2) := by
  rw [actualWireVertex_eq_port]
  exact ClauseEdges.incoming_body_iff φ (SatClauseOrder.permutation φ) o v hv

theorem outgoing_body_iff (φ : Formula n m) (o : Occurrence m)
    (v : PlanarSatAssembly.Vertex n m) (hv : CoreEdges.Body v) :
    (SatClauseOrder.graph φ).adj (actualWireVertex φ o true)
      (PermutationGraph.liftOriginal φ (SatClauseOrder.permutation φ) v) ↔
      v=clause o.1 (clauseTop o.2) := by
  rw [actualWireVertex_eq_port]
  exact ClauseEdges.outgoing_body_iff φ (SatClauseOrder.permutation φ) o v hv

/-- A complete single-edge certificate: adjacency, distinct endpoints,
simple unit-grid route, linear length, and clearance from every other
actual graph vertex. Pairwise interactions with other edge families are
handled separately. -/
theorem route_certificate (φ : Formula n m) (o : Occurrence m) (b : Bool) :
    (SatClauseOrder.graph φ).adj (source φ o b) (target φ o b) ∧
    source φ o b≠target φ o b ∧
    (route φ o b).head?=some (SatGlobalVertexPlacement.actualPoint φ (source φ o b)) ∧
    (route φ o b).getLast?=some (SatGlobalVertexPlacement.actualPoint φ (target φ o b)) ∧
    (route φ o b).Nodup ∧ (route φ o b).IsChain UnitStep ∧
    65≤(route φ o b).length ∧ (route φ o b).length≤1536*m ∧
    ∀ v,SatGlobalVertexPlacement.actualPoint φ v∈route φ o b ↔
      v=source φ o b ∨ v=target φ o b :=
  ⟨edge_is_arc φ o b,endpoints_ne φ o b,(route_endpoints φ o b).1,
    (route_endpoints φ o b).2,(route_simple φ o b).1,(route_simple φ o b).2,
    (route_length φ o b).1,(route_length φ o b).2,route_vertex_clear φ o b⟩

end GridHardness.SatClauseWireDrawing
