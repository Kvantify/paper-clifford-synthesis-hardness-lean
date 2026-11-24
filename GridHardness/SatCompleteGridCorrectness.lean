/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCompleteLayout
public import GridHardness.SatBipartiteCorrectness
public import GridHardness.GridAssemblyEncoding

/-!
# SAT Complete Grid Correctness

Semantic correctness of the completed SAT-to-grid construction. The actual
layout satisfies every geometric premise, and its encoded grid instance has
a Hamiltonian path exactly when the positive one-in-three formula is satisfiable.
The source-dependent layout is compiled by SatDirectedRecordsCode;
SatCompiledGridReduction packages the complete polynomial-cost reduction.
-/

@[expose] public section

namespace GridHardness.SatCompleteGridCorrectness
open CliffordComplexity CliffordSynthesis
open SatCompleteLayout GridProblems GridProblems.GridCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The final graph equivalence unfolds the assembled layout and its incidence relation.
set_option maxHeartbeats 1600000

/-- The four vertices replacing a sentinel exist even for the empty formula. -/
theorem vertex_card_lower (x : SatTy.denote) : 4 ≤ Fintype.card (SatBipartiteDrawing.Vertex x) := by
  obtain ⟨v⟩ := SatBipartiteCorrectness.directed_nonempty x
  have hi : Function.Injective (fun i : Fin 4 => (v,i) : Fin 4 → SatBipartiteDrawing.Vertex x) := by
    intro i j he
    exact congrArg Prod.snd he
  have h := Nat.card_le_card_of_injective
    (fun i : Fin 4 => (v,i) : Fin 4 → SatBipartiteDrawing.Vertex x) hi
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using h

theorem degree_le_three (x : SatTy.denote) (v : SatBipartiteDrawing.Vertex x) :
    (SatBipartiteDrawing.graph x).degree v ≤ 3 := by
  have h := SatBipartiteCorrectness.neighbor_card_le_three x v
  rw [Nat.card_eq_fintype_card] at h
  exact (SimpleGraph.card_neighborSet_eq_degree (SatBipartiteDrawing.graph x) v).symm ▸ h

/-- The finite induced grid of the actual assembly has a Hamiltonian cycle
exactly when the source positive one-in-three instance is satisfiable. -/
theorem induced_cycle_correct (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (hp : ∀ c ∈x, ∀ p ∈c, p.2 =true) :
    Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔
      ∃ (v : (layout x hw).Vertex) (p : (layout x hw).graph.Walk v v),
        p.IsHamiltonianCycle := by
  classical
  exact (SatBipartiteCorrectness.positiveSat_correct x hw hp).trans
    ((valid x hw).hamiltonianCycle_iff (Nat.le_trans (by decide) (vertex_card_lower x))
      (degree_le_three x)).symm

noncomputable def cycleInput (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) : CycleInputTy.denote :=
  (layout x hw).cycleInput

noncomputable def pathInput (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3) : InputTy.denote :=
  (layout x hw).pathInput

theorem cycle_correct (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (hp : ∀ c ∈x, ∀ p ∈c, p.2 =true) :
    Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔ GRID_HAMILTONIAN_CYCLE (cycleInput x hw) := by
  classical
  exact (SatBipartiteCorrectness.positiveSat_correct x hw hp).trans
    ((valid x hw).cycleInput_correct (Nat.le_trans (by decide) (vertex_card_lower x)) (degree_le_three x))

/-- No drawing, separation, port, or size premise is required from the caller. -/
theorem path_correct (x : SatTy.denote) (hw : ∀ c ∈x, c.length =3)
    (hp : ∀ c ∈x, ∀ p ∈c, p.2 =true) :
    Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔ GRID_HAMILTONIAN_PATH (pathInput x hw) := by
  classical
  exact (SatBipartiteCorrectness.positiveSat_correct x hw hp).trans
    ((valid x hw).pathInput_correct (Nat.le_trans (by decide) (vertex_card_lower x)) (degree_le_three x))

end GridHardness.SatCompleteGridCorrectness
