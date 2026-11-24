/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.PermutedTarget
public import CliffordSynthesis.HamiltonPath

/-!
# Permuted Rigidity

Global freshness fixes the output permutation of the replicated target.
-/

@[expose] public section

namespace CliffordSynthesis.PermutedRigidity

open Planes (F)
open StandardSpace (Space standard)
open RowExtraction (AddGate addRow runRows)
open RowHistory (Fresh newRow rowAt)
open RecorderVectors (embed parity recorder output)
open Target (Wire)
open DisplacedAlgebra

variable {d r n m : Nat}

/-- Only these kinds of vector can occur in a saturated history. -/
def Value (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F) (q : Space n) : Prop :=
  (∃ i, q = (standard n).x i) ∨ (∃ a, q = output label X a) ∨ ∃ v, q = parity label v

def Policy (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F) (cs : List (AddGate n)) : Prop :=
  ∀ pre g post, cs = pre ++ g :: post →
    (∃ a, newRow pre g (standard n).x = output label X a) ∨
    ∃ v, newRow pre g (standard n).x = parity label v

theorem prefix_value (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (hp : Policy label X cs)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post) (i : Fin n) :
    Value label X (runRows pre (standard n).x i) := by
  induction pre using List.reverseRecOn generalizing post with
  | nil => exact Or.inl ⟨i, rfl⟩
  | append_singleton pre g ih =>
    have heq' : cs = pre ++ g :: post := by simpa only [List.append_assoc, List.singleton_append] using heq
    rw [RowHistory.run_append, RowHistory.run_singleton]
    by_cases hi : i = g.target
    · subst i
      exact Or.inr (hp pre g post heq')
    · simpa only [addRow, ite_eq_right hi] using ih (g :: post) heq'

theorem value_recorder (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (q : Space n) (hq : Value label X q) (a : Fin r)
    (ha : q (recorder label a, false) = 1) :
    q = (standard n).x (recorder label a) ∨ q = output label X a := by
  rcases hq with ⟨i, rfl⟩ | ⟨b, rfl⟩ | ⟨v, rfl⟩
  · have hi : recorder label a = i := by by_contra h; simp [h] at ha
    exact Or.inl (by rw [hi])
  · have hab : a = b := by by_contra h; simp [RecorderVectors.output_recorder, h] at ha
    exact Or.inr (by rw [hab])
  · simp [RecorderVectors.parity_recorder] at ha

/-- The first production of q_a has exactly the operands y_a and f_a. -/
theorem output_operands (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (hf : Fresh cs (standard n).x) (hp : Policy label X cs)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post)
    (a : Fin r) (hq : newRow pre g (standard n).x = output label X a) :
    (runRows pre (standard n).x g.target = (standard n).x (recorder label a) ∧
      runRows pre (standard n).x g.control = parity label (X a)) ∨
    (runRows pre (standard n).x g.control = (standard n).x (recorder label a) ∧
      runRows pre (standard n).x g.target = parity label (X a)) := by
  have hneq (i : Fin n) : runRows pre (standard n).x i ≠ output label X a := by
    intro h
    exact hf pre g post heq pre.length le_rfl i (by
      simpa only [heq, RowHistory.at_prefix] using hq.trans h.symm)
  have hone := congrFun hq (recorder label a, false)
  rw [RowHistory.newRow_eq, Pi.add_apply, RecorderVectors.output_recorder, ite_eq_left rfl] at hone
  have h01 : ∀ x : F, x = 0 ∨ x = 1 := by decide
  have hsome : runRows pre (standard n).x g.target (recorder label a, false) = 1 ∨
      runRows pre (standard n).x g.control (recorder label a, false) = 1 := by
    rcases h01 (runRows pre (standard n).x g.target (recorder label a, false)) with h | h
    · exact Or.inr (by simpa only [h, zero_add] using hone)
    · exact Or.inl h
  have hsum : runRows pre (standard n).x g.target + runRows pre (standard n).x g.control =
      (standard n).x (recorder label a) + parity label (X a) := by
    simpa only [RowHistory.newRow_eq, output] using hq
  rcases hsome with ht | hc
  · have hh := value_recorder label X _ (prefix_value label X cs hp pre (g :: post) heq _) a ht
    rcases hh with hy | hq'
    · exact Or.inl ⟨hy, add_left_cancel (by simpa only [hy] using hsum)⟩
    · exact False.elim (hneq _ hq')
  · have hh := value_recorder label X _ (prefix_value label X cs hp pre (g :: post) heq _) a hc
    rcases hh with hy | hq'
    · exact Or.inr ⟨hy, add_left_cancel (by simpa only [hy, add_comm _ ((standard n).x (recorder label a))] using hsum)⟩
    · exact False.elim (hneq _ hq')

/-- Seeing a recorder output entails having seen its data parity earlier. -/
theorem output_source_seen (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (hf : Fresh cs (standard n).x) (hp : Policy label X cs)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post)
    (i : Fin n) (a : Fin r) (hq : runRows pre (standard n).x i = output label X a) :
    ∃ s ≤ pre.length, ∃ j, rowAt cs (standard n).x s j = parity label (X a) := by
  induction pre using List.reverseRecOn generalizing post with
  | nil => exact False.elim (RecorderVectors.output_not_initial label X a i hq)
  | append_singleton pre g ih =>
    have heq' : cs = pre ++ g :: post := by simpa only [List.append_assoc, List.singleton_append] using heq
    by_cases hi : i = g.target
    · have hnew : newRow pre g (standard n).x = output label X a := by
        simpa only [RowHistory.run_append, RowHistory.run_singleton, hi, newRow] using hq
      rcases output_operands label X cs hf hp pre post g heq' a hnew with ⟨_, hc⟩ | ⟨_, ht⟩
      · exact ⟨pre.length, by simp, g.control, by simpa only [heq', RowHistory.at_prefix] using hc⟩
      · exact ⟨pre.length, by simp, g.target, by simpa only [heq', RowHistory.at_prefix] using ht⟩
    · have hprev : runRows pre (standard n).x i = output label X a := by
        simpa only [RowHistory.run_append, RowHistory.run_singleton, addRow, ite_eq_right hi] using hq
      obtain ⟨s, hs, j, hj⟩ := ih (g :: post) heq' hprev
      exact ⟨s, by simp only [List.length_append, List.length_singleton]; omega, j, hj⟩

/-- Updating an untouched recorder must put its own output on that wire. -/
theorem first_recorder_update (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (cs : List (AddGate n)) (hf : Fresh cs (standard n).x) (hp : Policy label X cs)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post)
    (a : Fin r) (_ht : g.target = recorder label a)
    (hy : runRows pre (standard n).x g.target = (standard n).x (recorder label a)) :
    newRow pre g (standard n).x = output label X a := by
  rcases hp pre g post heq with ⟨b, hb⟩ | ⟨v, hv⟩
  · rcases output_operands label X cs hf hp pre post g heq b hb with ⟨hyt, _⟩ | ⟨_, hpt⟩
    · have hab : a = b := RecorderVectors.recorder_injective label
        (RowHistory.rows_injective [] (hy.symm.trans hyt))
      simpa only [hab] using hb
    · have hh := congrFun (hy.symm.trans hpt) (recorder label a, false)
      simp [RecorderVectors.parity_recorder] at hh
  · have hc : runRows pre (standard n).x g.control (recorder label a, false) = 1 := by
      have hh := congrFun hv (recorder label a, false)
      rw [RowHistory.newRow_eq, Pi.add_apply, hy, basis_at, ite_eq_left rfl,
        RecorderVectors.parity_recorder] at hh
      have h01 : ∀ x : F, x = 0 ∨ x = 1 := by decide
      rcases h01 (runRows pre (standard n).x g.control (recorder label a, false)) with h | h
      · simp [h] at hh
      · exact h
    rcases value_recorder label X _ (prefix_value label X cs hp pre (g :: post) heq _) a hc with hcy | hcq
    · exact False.elim (g.distinct (RowHistory.rows_injective pre (hcy.trans hy.symm)))
    · obtain ⟨s, hs, j, hj⟩ := output_source_seen label X cs hf hp pre (g :: post) heq g.control a hcq
      have hnew : newRow pre g (standard n).x = parity label (X a) := by
        rw [RowHistory.newRow_eq, hy, hcq, output, ← add_assoc, double, zero_add]
      exact False.elim (hf pre g post heq s hs j (hnew.trans hj.symm))

/-- A row whose final value differs from its initial value has a first update. -/
theorem first_update {V : Type*} [AddCommGroup V] (cs : List (AddGate n))
    (v : Fin n → V) (i : Fin n) (h : runRows cs v i ≠ v i) :
    ∃ pre g post, cs = pre ++ g :: post ∧ g.target = i ∧ runRows pre v i = v i := by
  induction cs generalizing v with
  | nil => exact False.elim (h rfl)
  | cons g cs ih =>
    by_cases ht : g.target = i
    · exact ⟨[], g, cs, rfl, ht, rfl⟩
    · have hsame : addRow g v i = v i := by simp [addRow, Ne.symm ht]
      have htail : runRows cs (addRow g v) i ≠ addRow g v i := by simpa only [RowHistory.run_cons, hsame] using h
      obtain ⟨pre, g', post, heq, ht', hv⟩ := ih (addRow g v) htail
      exact ⟨g :: pre, g', post, by simp [heq], ht', hv.trans hsame⟩

/-- No final row of the target is an untouched recorder basis vector. -/
theorem final_not_recorder_initial (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n))
    (t : Fin d → F) (X : Fin r → Fin d → F) (cs : List (AddGate n))
    (hout : ∀ i, runRows cs (standard n).x (perm i) = embed label (Target.matrix t X (label.symm i)))
    (a : Fin r) (i : Fin n) : runRows cs (standard n).x i ≠ (standard n).x (recorder label a) := by
  obtain ⟨j, rfl⟩ := perm.surjective i
  obtain ⟨w, rfl⟩ := label.surjective j
  rw [hout, Equiv.symm_apply_apply]
  rcases w with j | (_ | b)
  · rw [RecorderVectors.target_coordinate_row]
    intro h
    have hh := congrFun h (recorder label a, false)
    simp [recorder] at hh
  · rw [RecorderVectors.target_path_row]
    intro h
    have hh := congrFun h (recorder label a, false)
    simp [RecorderVectors.parity_recorder] at hh
  · rw [RecorderVectors.target_recorder_row]
    exact Ne.symm (RecorderVectors.output_not_initial label X b (recorder label a))

/-- Freshness and the allowed values force every coordinate and recorder to
finish on its original physical wire. The sole remaining path wire is fixed too. -/
theorem permutation_eq_one (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n))
    (t : Fin d → F) (X : Fin r → Fin d → F) (cs : List (AddGate n))
    (hf : Fresh cs (standard n).x) (hp : Policy label X cs)
    (hout : ∀ i, runRows cs (standard n).x (perm i) = embed label (Target.matrix t X (label.symm i))) :
    perm = Equiv.refl (Fin n) := by
  have hcoord (j : Fin d) : perm (label (.inl j)) = label (.inl j) := by
    apply Eq.symm
    apply RowRigidity.final_value_own_wire cs hf [] cs (by simp)
    simp only [RowHistory.run_nil, hout, Equiv.symm_apply_apply,
      RecorderVectors.target_coordinate_row]
  have hrec (a : Fin r) : perm (recorder label a) = recorder label a := by
    obtain ⟨pre, g, post, heq, ht, hy⟩ := first_update cs (standard n).x (recorder label a)
      (final_not_recorder_initial label perm t X cs hout a (recorder label a))
    have hnew := first_recorder_update label X cs hf hp pre post g heq a ht (by simpa only [ht] using hy)
    have hh := RowRigidity.final_value_own_wire cs hf (pre ++ [g]) post
      (by simpa only [List.append_assoc, List.singleton_append] using heq)
      g.target (perm (recorder label a)) (by
        rw [RowHistory.run_append, RowHistory.run_singleton, hout]
        simpa only [newRow, recorder, Equiv.symm_apply_apply, RecorderVectors.target_recorder_row] using hnew)
    exact (ht.symm.trans hh).symm
  have hpath : perm (label (.inr (.inl ()))) = label (.inr (.inl ())) := by
    obtain ⟨w, hw⟩ := label.surjective (perm (label (.inr (.inl ()))))
    rcases w with j | (_ | a)
    · have hh := label.injective (perm.injective (hw.symm.trans (hcoord j).symm))
      cases hh
    · exact hw.symm
    · have hh := label.injective (perm.injective (hw.symm.trans (hrec a).symm))
      cases hh
  apply Equiv.ext
  intro i
  obtain ⟨w, rfl⟩ := label.surjective i
  rcases w with j | (_ | a)
  · exact hcoord j
  · exact hpath
  · exact hrec a

/-- The output-permutation premise can be removed internally for every
budget-respecting row-addition implementation of a replicated target. -/
theorem replicated_permutation_eq_one (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n))
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (cs : List (AddGate n)) (t : Fin d → F)
    (hout : ∀ i, runRows cs (standard n).x (perm i) = embed label (Target.matrix t
      (ReplicatedTarget.repeated vertex copies) (label.symm i))) (hbudget : cs.length ≤ r + m) :
    perm = Equiv.refl (Fin n) := by
  apply permutation_eq_one label perm t _ cs
    (PermutedTarget.fresh label perm vertex hv hzero copies cs t hout hbudget) _ hout
  intro pre g post heq
  rcases PermutedTarget.birth_cases label perm vertex hv hzero copies cs t hout hbudget pre post g heq with h | ⟨v, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨vertex v.succ, h⟩

/-- Implementing a permuted target within budget yields
a Hamiltonian path, and in fact the permutation is forced to be the identity. -/
theorem permuted_soundness (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n))
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (gs : List (Circuit.Gate n)) (last : Fin (m + 1))
    (hfinal : ∀ i, (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))).x (perm i) =
      embed label (Target.matrix (vertex last) (ReplicatedTarget.repeated vertex copies) (label.symm i)))
    (hbudget : Circuit.cost gs ≤ r + m) :
    perm = Equiv.refl (Fin n) ∧ ∃ p : (HamiltonPath.cubeGraph vertex).Walk 0 last, p.IsHamiltonian := by
  obtain ⟨cs, hlen, hout⟩ := PermutedTarget.target_classical label perm vertex hv hzero copies gs
    (vertex last) hfinal hbudget
  have heq := replicated_permutation_eq_one label perm vertex hv hzero copies cs (vertex last) hout hlen.le
  refine ⟨heq, HamiltonPath.classical_implies_hamiltonian label vertex hv hzero copies cs last ?_ hlen.le⟩
  simpa only [heq, Equiv.refl_apply] using hout

end CliffordSynthesis.PermutedRigidity
