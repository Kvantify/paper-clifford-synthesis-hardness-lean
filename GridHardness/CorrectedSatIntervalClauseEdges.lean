/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalFalseEdges
public import GridHardness.CorrectedSatIntervalPermutationWirePlacement
public import GridHardness.SatClauseWireLattice

/-!
# Corrected SAT Interval Clause Edges

Exact clause-boundary edges in the completed permutation sweep.
Their wire endpoint is the false port of the first retained crossing, or
the original retired XOR when the occurrence has no crossing in its row.
-/

@[expose] public section

namespace GridHardness.CorrectedSatInterval.ClauseEdges
open PlanarSatAssembly GlobalNumbering
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))

noncomputable def port (j : Fin (3 *m)) (incoming : Bool) :
    (PermutationGraph.graph φ p).Vertex :=
  FalseEdges.runPort (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    j incoming

theorem incoming_iff (j : Fin (3 *m)) (v : PlanarSatAssembly.Vertex n m)
    (hv : CoreEdges.Body v) :
    (PermutationGraph.graph φ p).adj (PermutationGraph.liftOriginal φ p v)
      (port φ p j true) ↔
      Adj φ v (xor ((SatWireLayout.variableRank φ).symm j) 4) :=
  FalseEdges.run_incoming (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    j v (CoreEdges.initial_core φ v hv)

theorem outgoing_iff (j : Fin (3 *m)) (v : PlanarSatAssembly.Vertex n m)
    (hv : CoreEdges.Body v) :
    (PermutationGraph.graph φ p).adj (port φ p j false)
      (PermutationGraph.liftOriginal φ p v) ↔
      Adj φ (xor ((SatWireLayout.variableRank φ).symm j) 7) v :=
  FalseEdges.run_outgoing (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p)
    j v (CoreEdges.initial_core φ v hv)

theorem port_none (j : Fin (3 *m)) (hj : SatClauseWireLattice.firstRequest? p j =none)
    (incoming : Bool) :
    port φ p j incoming=PermutationGraph.liftOriginal φ p
      (xor ((SatWireLayout.variableRank φ).symm j) (FalseEdges.falsePort incoming)) := by
  apply FalseEdges.runPort_empty
  have hh := SatClauseWireLattice.firstRequest_val p j
  rw [hj] at hh
  apply List.head?_eq_none_iff.mp
  simpa using hh.symm

theorem port_some (i j : Fin (3 *m)) (hi : SatClauseWireLattice.firstRequest? p j =some i)
    (incoming : Bool) :
    port φ p j incoming=PermutationWirePlacement.fresh φ p
      ⟨(i,j),(SatClauseWireLattice.firstRequest_sound p i j hi).1⟩
      (FalseEdges.retainedPort incoming) := by
  have hh := SatClauseWireLattice.firstRequest_val p j
  rw [hi] at hh
  have hh' : (requests (permutationHeight p) (0+j.val)).head?=some i.val := by
    simpa using hh.symm
  unfold port
  rw [FalseEdges.runPort_fresh _ _ _ _ _ _ _ j i.val hh']
  unfold PermutationWirePlacement.fresh
  congr 1
  apply Fin.ext
  rw [PermutationWirePlacement.crossingEquiv_symm_val]
  simp only [FalseEdges.firstIndex,Nat.zero_add]

theorem source_incoming (o : Occurrence m) :
    Adj φ (clause o.1 (clauseBottom o.2)) (xor o 4) := by
  change (clause o.1 (clauseBottom o.2),xor o 4)∈edges φ
  simp only [edges,List.mem_append]
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨o,?_,?_⟩
  · exact (mem_occurrences o)
  · apply List.mem_append_left
    simp [clauseLinks]

theorem source_outgoing (o : Occurrence m) :
    Adj φ (xor o 7) (clause o.1 (clauseTop o.2)) := by
  change (xor o 7,clause o.1 (clauseTop o.2))∈edges φ
  simp only [edges,List.mem_append]
  apply Or.inr
  apply List.mem_flatMap.mpr
  refine ⟨o,?_,?_⟩
  · exact (mem_occurrences o)
  · apply List.mem_append_left
    simp [clauseLinks]

theorem incoming (o : Occurrence m) :
    (PermutationGraph.graph φ p).adj
      (PermutationGraph.liftOriginal φ p (clause o.1 (clauseBottom o.2)))
      (port φ p (SatWireLayout.variableRank φ o) true) := by
  rw [incoming_iff φ p _ _ (CoreEdges.clause_body _ _),Equiv.symm_apply_apply]
  exact source_incoming φ o

theorem outgoing (o : Occurrence m) :
    (PermutationGraph.graph φ p).adj
      (port φ p (SatWireLayout.variableRank φ o) false)
      (PermutationGraph.liftOriginal φ p (clause o.1 (clauseTop o.2))) := by
  rw [outgoing_iff φ p _ _ (CoreEdges.clause_body _ _),Equiv.symm_apply_apply]
  exact source_outgoing φ o

/-- No additional body vertex can acquire an edge into this clause-side
input during the crossing sweep. -/
theorem incoming_body_iff (o : Occurrence m) (v : PlanarSatAssembly.Vertex n m)
    (hv : CoreEdges.Body v) :
    (PermutationGraph.graph φ p).adj (PermutationGraph.liftOriginal φ p v)
      (port φ p (SatWireLayout.variableRank φ o) true) ↔
      v=clause o.1 (clauseBottom o.2) := by
  rw [incoming_iff φ p _ _ hv,Equiv.symm_apply_apply]
  constructor
  · intro h
    exact (xor_four_incoming φ o v h).resolve_left (fun he => hv o 5 he.symm)
  · rintro rfl
    exact source_incoming φ o

/-- The clause-side output has exactly its original clause top as body
successor, for every occurrence permutation. -/
theorem outgoing_body_iff (o : Occurrence m) (v : PlanarSatAssembly.Vertex n m)
    (hv : CoreEdges.Body v) :
    (PermutationGraph.graph φ p).adj (port φ p (SatWireLayout.variableRank φ o) false)
      (PermutationGraph.liftOriginal φ p v) ↔
      v=clause o.1 (clauseTop o.2) := by
  rw [outgoing_iff φ p _ _ hv,Equiv.symm_apply_apply]
  constructor
  · intro h
    exact (xor_seven_outgoing φ o v h).resolve_left (fun he => hv o 6 he.symm)
  · rintro rfl
    exact source_outgoing φ o

end GridHardness.CorrectedSatInterval.ClauseEdges
