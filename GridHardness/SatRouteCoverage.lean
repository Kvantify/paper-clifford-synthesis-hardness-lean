/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatBodyCoverage
public import GridHardness.SatRetiredCoverage
public import GridHardness.SatRetainedCoverage

/-!
# SAT Route Coverage

A graph-wide assembly of the route coverage proofs. The explicit
body-plus-wire equivalence combines the completed body, retired-XOR and
retained-crossing coverage proofs. No adjacency or drawing hypothesis remains.
-/

@[expose] public section

namespace GridHardness.SatRouteCoverage
open CliffordComplexity PlanarSatAssembly CorrectedSatInterval SatRouteCatalogue
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable (x : SatTy.denote)

/-- Completeness at the eight original XOR vertices of every retired wire. -/
def RetiredComplete : Prop :=
  ∀ (j : Fin (3*x.length)) (v : Fin 8),
    LocalComplete x (PermutationWirePlacement.vertex (finiteFormula x) (permutation x) (.inl (j,v)))

/-- Completeness at every retained vertex of each scheduled crossing cell. -/
def RetainedComplete : Prop :=
  ∀ (c : WireCrossingSchedule.Cell (permutation x)) (v : SatCrossingHorizontal.RetainedVertex),
    LocalComplete x (PermutationWirePlacement.vertex (finiteFormula x) (permutation x) (.inr (c,v)))

theorem wire_complete (hr : RetiredComplete x) (hc : RetainedComplete x)
    (w : SatGlobalVertexPlacement.WireVertex (finiteFormula x)) :
    LocalComplete x (PermutationWirePlacement.vertex (finiteFormula x) (permutation x) w) := by
  rcases w with ⟨j,v⟩ | ⟨c,v⟩
  · exact hr j v
  · exact hc c v

/-- Exhaustiveness follows from the actual vertex decomposition, rather
than from a presumed enumeration of the graph's edges. -/
theorem arc_covered_of_local (hr : RetiredComplete x) (hc : RetainedComplete x)
    (u v : Vertex x) (h : (SatClauseOrder.graph (finiteFormula x)).adj u v) :
    Covers x u v := by
  obtain ⟨a,rfl⟩ := (SatGlobalVertexPlacement.equiv (finiteFormula x)).surjective u
  obtain ⟨b,rfl⟩ := (SatGlobalVertexPlacement.equiv (finiteFormula x)).surjective v
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      rw [SatGlobalVertexPlacement.equiv_body,SatGlobalVertexPlacement.equiv_body] at h ⊢
      exact SatBodyCoverage.body_covered x a b h
    | inr b =>
      rw [SatGlobalVertexPlacement.equiv_wire] at h ⊢
      exact (wire_complete x hr hc b).1 _ h
  | inr a =>
    rw [SatGlobalVertexPlacement.equiv_wire] at h ⊢
    exact (wire_complete x hr hc a).2 _ h

/-- The already established soundness and the assembled coverage identify
the catalogue relation exactly with final-graph adjacency. -/
theorem covers_iff_adj_of_local (hr : RetiredComplete x) (hc : RetainedComplete x)
    (u v : Vertex x) :
    Covers x u v ↔ (SatClauseOrder.graph (finiteFormula x)).adj u v :=
  ⟨covers_arc x u v,arc_covered_of_local x hr hc u v⟩

theorem local_complete_of_local (hr : RetiredComplete x) (hc : RetainedComplete x)
    (v : Vertex x) : LocalComplete x v :=
  ⟨fun u h => arc_covered_of_local x hr hc u v h,fun u h => arc_covered_of_local x hr hc v u h⟩

/-- The original occurrence vertices satisfy the first local obligation. -/
theorem retired_complete : RetiredComplete x :=
  fun j v => SatRetiredCoverage.local_complete x j v

/-- The retained crossing vertices satisfy the second local obligation. -/
theorem retained_complete : RetainedComplete x := by
  intro c v
  rw [PermutationWirePlacement.vertex_fresh]
  exact SatRetainedCoverage.complete x c v

/-- Every arc of the completed clause-order SAT graph has a route index.
This semantic statement holds even for inputs outside width-three syntax. -/
theorem arc_covered (u v : Vertex x)
    (h : (SatClauseOrder.graph (finiteFormula x)).adj u v) : Covers x u v :=
  arc_covered_of_local x (retired_complete x) (retained_complete x) u v h

/-- Exact adjacency of the whole final graph in terms of the complete
simultaneous route catalogue. -/
theorem covers_iff_adj (u v : Vertex x) :
    Covers x u v ↔ (SatClauseOrder.graph (finiteFormula x)).adj u v :=
  ⟨covers_arc x u v,arc_covered x u v⟩

/-- Both incoming and outgoing adjacency are exhausted at every vertex. -/
theorem local_complete (v : Vertex x) : LocalComplete x v :=
  local_complete_of_local x (retired_complete x) (retained_complete x) v

end GridHardness.SatRouteCoverage
