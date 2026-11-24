/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatDegree
public import GridHardness.DirectedToBipartite

/-!
# Corrected SAT Degree Bipartite

The corrected, fully executed SAT crossing schedule followed by the
four-vertex directed-to-bipartite replacement. These are semantic graph
statements: no planar drawing or cost certificate is assumed or asserted.
-/

@[expose] public section

namespace GridHardness.CorrectedSatDegreeBipartite
open XorLineSchedule
open XorWire.NetworkDegree (inDegree outDegree)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

abbrev Vertex (g : FiniteGraph) := g.Vertex × Fin 4

noncomputable instance directedDecidableEq (g : FiniteGraph) : DecidableEq g.Vertex :=
  Classical.decEq _

def graph (g : FiniteGraph) : SimpleGraph (Vertex g) :=
  DirectedToBipartite.graph g.adj

instance graphDecidable (g : FiniteGraph) [Fintype g.Vertex] [DecidableEq g.Vertex]
    [DecidableRel g.adj] :
    DecidableRel (graph g).Adj := by
  unfold graph
  infer_instance

/-- The bipartition is explicitly the parity of the four-path position. -/
def coloring (g : FiniteGraph) : (graph g).Coloring (Fin 2) :=
  DirectedToBipartite.coloring g.adj

theorem colorable_two (g : FiniteGraph) : (graph g).Colorable 2 := ⟨coloring g⟩

theorem hamiltonianCycle_iff (g : FiniteGraph) (hn : Nonempty g.Vertex) :
    (∃ (v : Vertex g) (p : (graph g).Walk v v), p.IsHamiltonianCycle) ↔
      PathCover.Hamiltonian g.adj := by
  classical
  let _ : Fintype g.Vertex := Fintype.ofFinite _
  let _ : Nonempty g.Vertex := hn
  let _ : DecidableEq g.Vertex := directedDecidableEq g
  exact DirectedToBipartite.hamiltonianCycle_iff g.adj

theorem vertex_count (g : FiniteGraph) :
    Nat.card (Vertex g) = 4 * Nat.card g.Vertex := by
  rw [Nat.card_prod, Nat.card_fin, Nat.mul_comm]

/-- The maximum degree bound is independent of the chosen finite enumeration. -/
theorem degree_le_three (g : FiniteGraph) [Fintype g.Vertex]
    [DecidableEq g.Vertex] [DecidableRel g.adj]
    (hd : CorrectedSatDegree.Bounds g) (v : Vertex g) :
    (graph g).degree v ≤ 3 := by
  have h := (CorrectedSatDegree.bounds_iff g).mp hd
  apply DirectedToBipartite.degree_le_three g.adj
  · intro w
    have hw := (h w).1
    unfold inDegree at hw
    convert hw using 1
    congr 1
    ext u
    simp only [Finset.mem_filter]
  · intro w
    have hw := (h w).2.1
    unfold outDegree at hw
    convert hw using 1
    congr 1
    ext u
    simp only [Finset.mem_filter]

/-- Intrinsic formulation that does not require an enumeration argument. -/
theorem neighbor_card_le_three (g : FiniteGraph)
    (hd : CorrectedSatDegree.Bounds g) (v : Vertex g) :
    Nat.card {w : Vertex g // (graph g).Adj v w} ≤ 3 := by
  classical
  let _ : Fintype g.Vertex := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact (SimpleGraph.card_neighborSet_eq_degree (graph g) v).trans_le
    (degree_le_three g hd v)

theorem scheduled_nonempty {n m : Nat} (φ : PlanarSatAssembly.Formula n m)
    (cells : List (Nat × Nat)) : Nonempty (CorrectedSatSchedule.graph φ cells).Vertex := by
  have h := CorrectedSatSchedule.vertex_count φ cells
  exact (Nat.card_pos_iff.mp (by omega)).1

theorem scheduled_correct {n m : Nat} (φ : PlanarSatAssembly.Formula n m)
    (cells : List (Nat × Nat)) :
    (∃ (v : Vertex (CorrectedSatSchedule.graph φ cells))
      (p : (graph (CorrectedSatSchedule.graph φ cells)).Walk v v), p.IsHamiltonianCycle) ↔
      PlanarSatAssembly.Satisfiable φ :=
  (hamiltonianCycle_iff _ (scheduled_nonempty φ cells)).trans
    (CorrectedSatSchedule.correct φ cells).symm

theorem scheduled_vertex_count {n m : Nat} (φ : PlanarSatAssembly.Formula n m)
    (cells : List (Nat × Nat)) :
    Nat.card (Vertex (CorrectedSatSchedule.graph φ cells)) =
      4 * (3 + 2*n + 36*m + 40*(CorrectedSatSchedule.plan (3*m) cells).length) := by
  rw [vertex_count, CorrectedSatSchedule.vertex_count]

theorem scheduled_vertex_bound {n m : Nat} (φ : PlanarSatAssembly.Formula n m)
    (cells : List (Nat × Nat)) :
    Nat.card (Vertex (CorrectedSatSchedule.graph φ cells)) ≤
      4 * (3 + 2*n + 36*m + 360*m*m) := by
  rw [vertex_count]
  exact Nat.mul_le_mul_left 4 (CorrectedSatSchedule.vertex_bound φ cells)

theorem positive_nonempty (x : CliffordComplexity.SatTy.denote) :
    Nonempty (CorrectedSatSchedule.positiveGraph x).Vertex := by
  unfold CorrectedSatSchedule.positiveGraph
  split
  · exact scheduled_nonempty _ _
  · exact ⟨(0 : Fin 2)⟩

/-- The vertex count includes one contribution for each scheduled crossing. -/
theorem actual_vertex_count (x : CliffordComplexity.SatTy.denote) :
    Nat.card (Vertex (CorrectedSatSchedule.actualGraph x)) =
      4 * (3 + 2*((CliffordComplexity.vsOf x).length+1) + 36*x.length +
        40*(SatCrossingCode.crossings.eval x).length) := by
  rw [vertex_count, CorrectedSatSchedule.actual_vertex_count]

/-- For malformed positive syntax the target is the four-path conversion of
the concrete two-vertex edgeless directed graph, hence has eight vertices. -/
theorem positive_vertex_count (x : CliffordComplexity.SatTy.denote) :
    Nat.card (Vertex (CorrectedSatSchedule.positiveGraph x)) =
      if CorrectedSatSchedule.validSyntax x then
        4 * (3 + 2*((CliffordComplexity.vsOf x).length+1) + 36*x.length +
          40*(SatCrossingCode.crossings.eval x).length) else 8 := by
  unfold CorrectedSatSchedule.positiveGraph
  split
  · exact actual_vertex_count x
  · rw [vertex_count]
    simp [CorrectedSatSchedule.invalidGraph]

/-- A polynomial vertex bound in the intermediate positive formula's
variables and clauses. This statement makes no compiler cost claim. -/
theorem positive_vertex_bound (x : CliffordComplexity.SatTy.denote) :
    Nat.card (Vertex (CorrectedSatSchedule.positiveGraph x)) ≤
      4 * (3 + 2*((CliffordComplexity.vsOf x).length+1) + 36*x.length + 360*x.length*x.length) := by
  unfold CorrectedSatSchedule.positiveGraph
  split
  · rw [vertex_count]
    exact Nat.mul_le_mul_left 4 (CorrectedSatSchedule.actual_vertex_bound x)
  · rw [vertex_count]
    simp only [CorrectedSatSchedule.invalidGraph, Nat.card_fin]
    omega

end
end GridHardness.CorrectedSatDegreeBipartite
