/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.FullSynthesisColumns
public import CliffordSynthesis.GeneralReduction

/-!
# Full Synthesis Permutations

Reordering output wires and changing the two-qubit gate set preserve the column pairings.
-/

public section

namespace CliffordSynthesis.FreeSwaps

open Circuit

variable {n : Nat}

theorem columnsSymplectic_reorder (perm : Equiv.Perm (Fin n)) {a : Tableau n}
    (ha : ColumnsSymplectic a) : ColumnsSymplectic (reorder perm a) := by
  intro p q
  rw [← ha p q]
  exact Fintype.sum_equiv perm _ _ (fun _ => rfl)

theorem columnsSymplectic_execute {a : Tableau n} (ha : ColumnsSymplectic a) (gs : List (Step n)) :
    ColumnsSymplectic (execute gs a) := by
  rw [normalize_run]
  exact columnsSymplectic_reorder _ (ha.run _)

end CliffordSynthesis.FreeSwaps

namespace CliffordSynthesis.TwoQubit.StepWithSwap

theorem columnsSymplectic_run {n : Nat} {a : Circuit.Tableau n} (ha : Circuit.ColumnsSymplectic a)
    (gs : List (StepWithSwap n)) : Circuit.ColumnsSymplectic (run gs a) := by
  obtain ⟨ss, _, he⟩ := to_cnot gs
  rw [← he]
  exact FreeSwaps.columnsSymplectic_execute ha ss

end CliffordSynthesis.TwoQubit.StepWithSwap
