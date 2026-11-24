/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.RowHistory

/-!
# Row Rigidity

Consequences of global freshness for the physical locations of final rows.
In particular, an output cannot be manufactured on a wrong wire and moved later.
-/

public section

namespace CliffordSynthesis.RowRigidity

open Planes (F)
open RowExtraction (AddGate addRow runRows)
open RowHistory (rowAt newRow Fresh)
open StandardSpace (standard)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

omit [Module F V] in
/-- If no update creates q, a final q was already on that same wire initially. -/
theorem final_existing (cs : List (AddGate n)) (v : Fin n → V) (j : Fin n) (q : V)
    (hout : runRows cs v j = q)
    (hn : ∀ pre g post, cs = pre ++ g :: post → newRow pre g v ≠ q) : v j = q := by
  induction cs generalizing v with
  | nil => exact hout
  | cons g cs ih =>
    have hh : addRow g v j = q := by
      apply ih _ hout
      intro pre h post heq
      exact hn (g :: pre) h post (by simp [heq])
    by_cases hj : j = g.target
    · exact False.elim (hn [] g cs rfl (by simpa only [newRow, RowHistory.run_nil, hj] using hh))
    · simpa only [addRow, ite_eq_right hj] using hh

/-- A final row value that has already appeared cannot be acquired anew in the
remaining suffix. Therefore it is already on its final physical wire. -/
theorem seen_final_prefix (cs : List (AddGate n)) (hf : Fresh cs (standard n).x)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post) (s : Nat) (hs : s ≤ pre.length)
    (i j : Fin n) (hv : runRows cs (standard n).x j = rowAt cs (standard n).x s i) :
    runRows pre (standard n).x j = rowAt cs (standard n).x s i := by
  apply final_existing post (runRows pre (standard n).x) j _
    (by simpa only [heq, RowHistory.run_append] using hv)
  intro ps g tail hpost
  have hcs : cs = (pre ++ ps) ++ g :: tail := by simp [heq, hpost, List.append_assoc]
  have hh := hf (pre ++ ps) g tail hcs s (by simp only [List.length_append]; omega) i
  simpa only [newRow, RowHistory.run_append] using hh

theorem final_value_own_wire (cs : List (AddGate n)) (hf : Fresh cs (standard n).x)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post) (i j : Fin n)
    (hv : runRows pre (standard n).x i = runRows cs (standard n).x j) : i = j := by
  have hh := seen_final_prefix cs hf pre post heq pre.length le_rfl i j
    (by simpa only [heq, RowHistory.at_prefix] using hv.symm)
  apply RowHistory.rows_injective pre
  simpa only [heq, RowHistory.at_prefix] using hh.symm

/-- A coordinate row with its initial value prescribed finally is never altered. -/
theorem restored_initial_fixed (cs : List (AddGate n)) (hf : Fresh cs (standard n).x)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post) (i : Fin n)
    (hfinal : runRows cs (standard n).x i = (standard n).x i) :
    runRows pre (standard n).x i = (standard n).x i := by
  have hh := seen_final_prefix cs hf pre post heq 0 (Nat.zero_le _) i i
    (by simpa only [rowAt, List.take_zero, RowHistory.run_nil] using hfinal)
  simpa only [rowAt, List.take_zero, RowHistory.run_nil] using hh

theorem restored_initial_not_target (cs : List (AddGate n)) (hf : Fresh cs (standard n).x)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post) (i : Fin n)
    (hfinal : runRows cs (standard n).x i = (standard n).x i) : g.target ≠ i := by
  intro ht
  have hb := restored_initial_fixed cs hf pre (g :: post) heq i hfinal
  have ha := restored_initial_fixed cs hf (pre ++ [g]) post
    (by simpa only [List.append_assoc, List.singleton_append] using heq) i hfinal
  apply RowHistory.target_changes pre g
  rw [RowHistory.run_append, RowHistory.run_singleton] at ha
  simpa only [newRow, ht] using ha.trans hb.symm

/-- A vanished input column cannot reappear under subsequent row additions. -/
theorem zero_column (cs : List (AddGate n)) (v : Fin n → StandardSpace.Space n)
    (p : Fin n × Bool) (hz : ∀ i, v i p = 0) : ∀ i, runRows cs v i p = 0 := by
  induction cs generalizing v with
  | nil => exact hz
  | cons g cs ih =>
    apply ih
    intro i
    simp only [addRow]
    split_ifs
    · simp [Pi.add_apply, hz]
    · exact hz i

end CliffordSynthesis.RowRigidity
