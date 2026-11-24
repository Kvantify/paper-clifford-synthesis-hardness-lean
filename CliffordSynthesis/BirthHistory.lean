/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.BirthOccurrences
public import CliffordSynthesis.PairOrigins

/-!
# Birth History

Timeline lemmas for reasoning about designated births and earlier visible
values. Indices count all gates, including the free local gates.
-/

public section

namespace CliffordSynthesis.BirthHistory

open Planes (F)
open SymplecticCircuit (Rows run applyGate)
open BirthOccurrences (Occurrence occurrences atTime)
open Observation (visible)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

theorem atTime_prefix (W : Submodule F V) (pre post : List (Circuit.Gate n)) (a : Rows n V) (i : Fin n) :
    atTime W (pre ++ post) a pre.length i = visible W (run pre a) i := by
  simp [atTime]

theorem atTime_after (W : Submodule F V) (pre post : List (Circuit.Gate n))
    (a : Rows n V) (g : Circuit.Gate n) (i : Fin n) :
    atTime W (pre ++ g :: post) a (pre.length + 1) i = visible W (applyGate g (run pre a)) i := by
  simp [atTime, List.take_append, List.take_of_length_le (Nat.le_succ pre.length), PairOrigins.run_append, run]

theorem atTime_prefix_of_prefix (W : Submodule F V) (gs pre : List (Circuit.Gate n))
    (a : Rows n V) (i : Fin n) (h : pre.IsPrefix gs) :
    atTime W gs a pre.length i = visible W (run pre a) i := by
  obtain ⟨post, rfl⟩ := h
  exact atTime_prefix W pre post a i

/-- Until a wire's first birth, its only possible nonzero visible value is
the value it carried initially; hidden intervals are allowed. -/
theorem visible_before_birth (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (i : Fin n) (k : Nat) (hn : ∀ l < k, (l, i) ∉ occurrences W gs a)
    (s : Nat) (hsk : s ≤ k) (hs : s ≤ gs.length) (v : V)
    (hv : atTime W gs a s i = some v) : visible W a i = some v := by
  induction s with
  | zero => simpa [atTime, run] using hv
  | succ s ih =>
    by_cases hp : atTime W gs a s i = some v
    · exact ih (by omega) (by omega) hp
    · have hb : (s, i) ∈ occurrences W gs a := by
        apply (BirthOccurrences.occurrence_iff W gs a s i).mpr
        refine ⟨by omega, ?_, ?_⟩
        · simp [show atTime W gs a (s + 1) i = some v from hv]
        · rw [show atTime W gs a (s + 1) i = some v from hv]
          exact Ne.symm hp
      exact False.elim (hn s (by omega) hb)

/-- An occurrence in a prefix remains the same occurrence in the full circuit. -/
theorem prefix_occurrences (W : Submodule F V) (pre post : List (Circuit.Gate n)) (a : Rows n V) :
    occurrences W pre a ⊆ occurrences W (pre ++ post) a := by
  induction pre generalizing a with
  | nil => simp [occurrences]
  | cons g pre ih =>
    simp only [List.cons_append, BirthOccurrences.occurrences_cons]
    exact Finset.union_subset_union (by rfl) (Finset.image_mono _ (ih (applyGate g a)))

/-- Every noninitial visible value at a prefix has a birth carrying that value
in the full history, at or before the end of that prefix. -/
theorem prefix_value_has_birth (W : Submodule F V) (pre post : List (Circuit.Gate n))
    (a : Rows n V) (i : Fin n) (v : V) (hv : visible W (run pre a) i = some v)
    (hi : visible W a i ≠ some v) :
    ∃ k, (k, i) ∈ occurrences W (pre ++ post) a ∧ k < pre.length ∧
      atTime W (pre ++ post) a (k + 1) i = some v := by
  obtain ⟨k, hk, hnew, _⟩ := BirthOccurrences.final_appearance W pre a i v hv hi
  have hlt := BirthOccurrences.occurrence_time_lt W pre a (k, i) hk
  refine ⟨k, prefix_occurrences W pre post a hk, hlt, ?_⟩
  simpa only [atTime, List.take_append_of_le_length (by omega : k + 1 ≤ pre.length)] using hnew

end CliffordSynthesis.BirthHistory
