/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalGlobalNumbering

/-!
# Corrected SAT Interval Permutation Graph

Choose the vertical order of occurrence wires independently of the
original SAT graph. The original variable-order labels and initial graph
are unchanged. Every permutation gives a Hamiltonicity-preserving sweep;
compatibility with a particular placement of clause bodies is a separate
geometric obligation. The canonical construction is recovered by choosing
the original occurrence permutation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness.CorrectedSatInterval.PermutationGraph
open PlanarSatAssembly XorLineRegistry XorLineSchedule

theorem initial_ready {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    Ready (initialState φ) (permutationHeight p) 0 where
  bound := fun b => b.elim
  covered := by intro i k hi; omega

def finalState {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    IntervalState 0 :=
  runState (permutationHeight p) (permutationHeight_injective p) (permutationHeight_pos p)
    (3*m) 0 (initialState φ) (initial_ready φ p)

def graph {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) : FiniteGraph :=
  (finalState φ p).toFiniteGraph

theorem canonical_graph {n m : Nat} (φ : Formula n m) :
    graph φ (SatWireLayout.permutation φ) = CorrectedSatInterval.graph φ := rfl

theorem canonical_finalState {n m : Nat} (φ : Formula n m) :
    finalState φ (SatWireLayout.permutation φ) = CorrectedSatInterval.finalState φ := rfl

theorem correct {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    Satisfiable φ ↔ PathCover.Hamiltonian (graph φ p).adj :=
  (PlanarSatReduction.correct φ).trans
    (run_correct (permutationHeight p) (permutationHeight_injective p) (permutationHeight_pos p)
      (3*m) 0 (initialState φ) (initial_ready φ p))

theorem vertex_count {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    Nat.card (graph φ p).Vertex =
      3+2*n+36*m+40*moveCount (permutationHeight p) (3*m) 0 := by
  change Nat.card
    (run (permutationHeight p) (permutationHeight_injective p) (permutationHeight_pos p)
      (3*m) 0 (initialState φ) (initial_ready φ p)).Vertex = _
  rw [run_vertex_count]
  change Nat.card (PlanarSatAssembly.Vertex n m)+_=_
  rw [Nat.card_eq_fintype_card,PlanarSatAssembly.vertex_card]

theorem vertex_bound {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    Nat.card (graph φ p).Vertex ≤ 3+2*n+36*m+360*m*m := by
  rw [vertex_count]
  have h := moveCount_le (permutationHeight p) (3*m) 0
  nlinarith

theorem final_enum_length_le {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    (finalState φ p).enum.length ≤ 3*m+2*moveCount (permutationHeight p) (3*m) 0 := by
  have h := runState_enum_length_le (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (initial_ready φ p)
  change (finalState φ p).enum.length ≤ 0+3*m+2*moveCount (permutationHeight p) (3*m) 0 at h
  simpa only [Nat.zero_add] using h

/-- The execution trace is exactly the inversion set of the chosen height
permutation, regardless of the original formula's clause order. -/
theorem covers_inversion {N : Nat} (p : Equiv.Perm (Fin N)) (i j : Fin N) :
    (i.val,j.val) ∈ trace (permutationHeight p) N 0 ↔ i<j ∧ p j<p i := by
  rw [mem_trace]
  simp only [permutationHeight_apply]
  have hj := j.isLt
  simp only [Nat.zero_le, Nat.zero_add, true_and]
  constructor
  · intro h
    exact ⟨h.1,by simpa using h.2.1⟩
  · intro h
    exact ⟨h.1,by simpa using h.2,hj⟩

/-- The same explicit original blocks followed by forty fresh names per
crossing, for the selected height order. -/
noncomputable def number {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    (graph φ p).Vertex ≃ Fin (3+2*n+36*m+40*moveCount (permutationHeight p) (3*m) 0) :=
  GlobalNumbering.runEquiv (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (3+2*n+36*m)
    (initialState φ) (initial_ready φ p) (GlobalNumbering.initialEquiv φ)

noncomputable def liftOriginal {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m))) :
    PlanarSatAssembly.Vertex n m → (graph φ p).Vertex :=
  GlobalNumbering.runLift (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (initialState φ) (initial_ready φ p)

theorem original_names {n m : Nat} (φ : Formula n m) (p : Equiv.Perm (Fin (3 *m)))
    (v : PlanarSatAssembly.Vertex n m) :
    (number φ p (liftOriginal φ p v)).val = (PlanarSatCode.numbering n m).num v :=
  GlobalNumbering.runLift_names (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (3+2*n+36*m)
    (initialState φ) (initial_ready φ p) (GlobalNumbering.initialEquiv φ) v

theorem liftOriginal_injective {n m : Nat} (φ : Formula n m)
    (p : Equiv.Perm (Fin (3 *m))) : Function.Injective (liftOriginal φ p) :=
  GlobalNumbering.runLift_injective (permutationHeight p) (permutationHeight_injective p)
    (permutationHeight_pos p) (3*m) 0 (3+2*n+36*m)
    (initialState φ) (initial_ready φ p) (GlobalNumbering.initialEquiv φ)

end GridHardness.CorrectedSatInterval.PermutationGraph
