/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.ClassicalTarget

/-!
# Recorder Rigidity

Private recorder columns cannot be lost and recreated by row additions.
This proves the recorder restriction without assuming a rank bound.
-/

@[expose] public section

namespace CliffordSynthesis.RecorderRigidity

open Planes (F)
open RowExtraction (AddGate addRow runRows)
open RowHistory (newRow Fresh)
open StandardSpace (Space standard)
open RecorderVectors (recorder output parity)
open Target (Wire)

variable {d r n : Nat}

def Allowed (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F) (q : Space n) : Prop :=
  (∃ a, q = output label X a) ∨ ∀ a, q (recorder label a, false) = 0

def Policy (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F) (cs : List (AddGate n)) : Prop :=
  ∀ pre g post, cs = pre ++ g :: post → Allowed label X (newRow pre g (standard n).x)

theorem output_birth_own (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (hf : Fresh cs (standard n).x)
    (hfinal : ∀ a, runRows cs (standard n).x (recorder label a) = output label X a)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post)
    (a : Fin r) (hq : newRow pre g (standard n).x = output label X a) : g.target = recorder label a := by
  apply RowRigidity.final_value_own_wire cs hf (pre ++ [g]) post
    (by simpa only [List.append_assoc, List.singleton_append] using heq) g.target (recorder label a)
  rw [RowHistory.run_append, RowHistory.run_singleton, hfinal]
  exact hq

/-- Every private recorder column is zero outside its own physical row. -/
theorem private_column (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (hf : Fresh cs (standard n).x) (hp : Policy label X cs)
    (hfinal : ∀ a, runRows cs (standard n).x (recorder label a) = output label X a)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post) (a : Fin r) :
    ∀ i, i ≠ recorder label a → runRows pre (standard n).x i (recorder label a, false) = 0 := by
  induction pre using List.reverseRecOn generalizing post with
  | nil =>
    intro i hi
    simp [RowHistory.run_nil, standard, Prod.mk.injEq, Ne.symm hi]
  | append_singleton pre g ih =>
    have heq' : cs = pre ++ g :: post := by simpa only [List.append_assoc, List.singleton_append] using heq
    have hh := ih (g :: post) heq'
    intro i hi
    rw [RowHistory.run_append, RowHistory.run_singleton]
    by_cases hit : i = g.target
    · subst i
      change newRow pre g (standard n).x (recorder label a, false) = 0
      rcases hp pre g post heq' with ⟨b, hb⟩ | hz
      · have ht := output_birth_own label X cs hf hfinal pre post g heq' b hb
        have hab : a ≠ b := by intro h; subst b; exact hi ht
        rw [hb, RecorderVectors.output_recorder]
        exact ite_eq_right hab
      · exact hz a
    · simpa only [addRow, ite_eq_right hit] using hh i hi

/-- The own-row entry of every recorder column remains one. If it vanished,
the whole column would be zero and no later row addition could recover it. -/
theorem recorder_coordinate (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (hf : Fresh cs (standard n).x) (hp : Policy label X cs)
    (hfinal : ∀ a, runRows cs (standard n).x (recorder label a) = output label X a)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post) (a : Fin r) :
    runRows pre (standard n).x (recorder label a) (recorder label a, false) = 1 := by
  have h01 : ∀ x : F, x = 0 ∨ x = 1 := by decide
  rcases h01 (runRows pre (standard n).x (recorder label a) (recorder label a, false)) with hz | ho
  · have hzall : ∀ i, runRows pre (standard n).x i (recorder label a, false) = 0 := by
      intro i
      by_cases hi : i = recorder label a
      · simpa only [hi] using hz
      · exact private_column label X cs hf hp hfinal pre post heq a i hi
    have hh := RowRigidity.zero_column post (runRows pre (standard n).x) (recorder label a, false) hzall (recorder label a)
    rw [← RowHistory.run_append, ← heq, hfinal, RecorderVectors.output_recorder] at hh
    simp at hh
  · exact ho

theorem recorder_birth_output (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (hf : Fresh cs (standard n).x) (hp : Policy label X cs)
    (hfinal : ∀ a, runRows cs (standard n).x (recorder label a) = output label X a)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post)
    (a : Fin r) (ht : g.target = recorder label a) : newRow pre g (standard n).x = output label X a := by
  rcases hp pre g post heq with ⟨b, hb⟩ | hz
  · have ht' := output_birth_own label X cs hf hfinal pre post g heq b hb
    have hab := RecorderVectors.recorder_injective label (ht.symm.trans ht')
    simpa only [hab] using hb
  · have hh := recorder_coordinate label X cs hf hp hfinal (pre ++ [g]) post
      (by simpa only [List.append_assoc, List.singleton_append] using heq) a
    rw [RowHistory.run_append, RowHistory.run_singleton] at hh
    have hzero := hz a
    change addRow g (runRows pre (standard n).x) g.target (recorder label a, false) = 0 at hzero
    rw [ht, hh] at hzero
    simp at hzero

/-- At every prefix, each recorder is either untouched or already its final row. -/
theorem recorder_row_form (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (hf : Fresh cs (standard n).x) (hp : Policy label X cs)
    (hfinal : ∀ a, runRows cs (standard n).x (recorder label a) = output label X a)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post) (a : Fin r) :
    runRows pre (standard n).x (recorder label a) = (standard n).x (recorder label a) ∨
      runRows pre (standard n).x (recorder label a) = output label X a := by
  induction pre using List.reverseRecOn generalizing post with
  | nil => exact Or.inl rfl
  | append_singleton pre g ih =>
    have heq' : cs = pre ++ g :: post := by simpa only [List.append_assoc, List.singleton_append] using heq
    rw [RowHistory.run_append, RowHistory.run_singleton]
    by_cases ht : g.target = recorder label a
    · exact Or.inr (by simpa only [newRow, ht] using recorder_birth_output label X cs hf hp hfinal pre post g heq' a ht)
    · simpa only [addRow, ite_eq_right (Ne.symm ht)] using ih (g :: post) heq'

theorem recorder_not_twice (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (hf : Fresh cs (standard n).x) (hp : Policy label X cs)
    (hfinal : ∀ a, runRows cs (standard n).x (recorder label a) = output label X a)
    (pre middle post : List (AddGate n)) (g h : AddGate n)
    (heq : cs = pre ++ g :: (middle ++ h :: post)) (a : Fin r)
    (hg : g.target = recorder label a) : h.target ≠ recorder label a := by
  intro hh
  have hfirst := recorder_birth_output label X cs hf hp hfinal pre (middle ++ h :: post) g heq a hg
  have heq' : cs = (pre ++ g :: middle) ++ h :: post := by simp [heq, List.append_assoc]
  have hsecond := recorder_birth_output label X cs hf hp hfinal (pre ++ g :: middle) post h heq' a hh
  have hfr := hf (pre ++ g :: middle) h post heq' (pre.length + 1)
    (by simp only [List.length_append, List.length_cons]; omega) g.target
  rw [hsecond] at hfr
  apply hfr
  rw [heq, RowHistory.at_after]
  exact hfirst.symm

/-- The concrete target supplies the allowed-value policy internally. -/
theorem target_policy {m : Nat} (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (cs : List (AddGate n)) (t : Fin d → F)
    (hout : ∀ i, runRows cs (standard n).x i = RecorderVectors.embed label (Target.matrix t
      (ReplicatedTarget.repeated vertex copies) (label.symm i))) (hbudget : cs.length ≤ r + m) :
    Policy label (ReplicatedTarget.repeated vertex copies) cs := by
  intro pre g post heq
  rcases ClassicalTarget.birth_cases label vertex hv hzero copies cs t hout hbudget pre post g heq with hq | ⟨v, hv⟩
  · exact Or.inl hq
  · exact Or.inr (fun a => by rw [hv, RecorderVectors.parity_recorder])

end CliffordSynthesis.RecorderRigidity
