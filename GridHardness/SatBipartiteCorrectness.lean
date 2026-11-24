/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBipartiteEdges
public import GridHardness.CorrectedSatDegreeBipartite

/-!
# SAT Bipartite Correctness

Semantic correctness of the exact bipartite graph carrying the drawing.
It is the four-path conversion of the completed permutation sweep, so its
Hamiltonian cycles encode precisely the original finite formula. These
statements do not assert a cost-certified compiler to the drawn graph.
-/

@[expose] public section

namespace GridHardness.SatBipartiteCorrectness
open CliffordComplexity PlanarSatAssembly SatBipartiteEdges
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- A sentinel supplies an actual vertex even when the formula is empty. -/
theorem directed_nonempty (x : SatTy.denote) :
    Nonempty (SatClauseOrder.graph (finiteFormula x)).Vertex :=
  ⟨SatGlobalVertexPlacement.equiv (finiteFormula x) (.inl (.inl 0))⟩

/-- The graph whose edges and routes are catalogued has a Hamiltonian
cycle exactly when the underlying finite one-in-three formula is satisfiable. -/
theorem graph_hamiltonian_iff (x : SatTy.denote) :
    (∃ (v : Vertex x) (p : (graph x).Walk v v), p.IsHamiltonianCycle) ↔
      Satisfiable (finiteFormula x) :=
  (CorrectedSatDegreeBipartite.hamiltonianCycle_iff
    (SatClauseOrder.graph (finiteFormula x)) (directed_nonempty x)).trans
    (SatClauseOrder.correct (finiteFormula x)).symm

/-- Agreement with the encoded positive one-in-three SAT predicate on
well-formed positive clauses of width three. -/
theorem positiveSat_correct (x : SatTy.denote)
    (hw : ∀ c ∈x, c.length =3) (hp : ∀ c ∈x, ∀ p ∈c, p.2 =true) :
    Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔
      ∃ (v : Vertex x) (p : (graph x).Walk v v), p.IsHamiltonianCycle :=
  (finiteFormula_correct x hw hp).symm.trans (graph_hamiltonian_iff x).symm

/-- Path-position parity supplies the graph's bipartition. -/
def coloring (x : SatTy.denote) : (graph x).Coloring (Fin 2) :=
  DirectedToBipartite.coloring (SatClauseOrder.graph (finiteFormula x)).adj

theorem colorable_two (x : SatTy.denote) : (graph x).Colorable 2 := ⟨coloring x⟩

/-- The actual drawn graph has maximum degree at most three, stated
without choosing a finite enumeration of its vertices. -/
theorem neighbor_card_le_three (x : SatTy.denote) (v : Vertex x) :
    Nat.card {w : Vertex x // (graph x).Adj v w} ≤ 3 :=
  CorrectedSatDegreeBipartite.neighbor_card_le_three
    (SatClauseOrder.graph (finiteFormula x))
    (DirectedIncidenceSaturation.permutation_bounds (finiteFormula x)
      (SatClauseOrder.permutation (finiteFormula x))) v

end GridHardness.SatBipartiteCorrectness
