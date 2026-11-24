/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.RecorderRigidity

/-!
# Path Rows

The remaining data updates target the path wire and are controlled by
unchanged coordinate rows. All hypotheses are instantiated from a target run.
-/

@[expose] public section

namespace CliffordSynthesis.PathRows

open Planes (F)
open RowExtraction (AddGate addRow runRows)
open RowHistory (newRow Fresh)
open StandardSpace (Space standard)
open RecorderVectors (recorder output parity embed)
open Target (Wire)

variable {d r n m : Nat}

def pathWire (label : Wire d r ≃ Fin n) : Fin n := label (.inr (.inl ()))

/-- Internal consequences of saturation, rather than additional source facts. -/
structure Certified (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) (cs : List (AddGate n)) : Prop where
  fresh : Fresh cs (standard n).x
  births : ∀ pre g post, cs = pre ++ g :: post →
    (∃ a, newRow pre g (standard n).x = output label X a) ∨
      ∃ v : Fin m, newRow pre g (standard n).x = parity label (vertex v.succ)
  outputs : ∀ a, runRows cs (standard n).x (recorder label a) = output label X a
  coordinates : ∀ j, runRows cs (standard n).x (label (.inl j)) = (standard n).x (label (.inl j))

theorem certified_target (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (cs : List (AddGate n)) (t : Fin d → F)
    (hout : ∀ i, runRows cs (standard n).x i = embed label (Target.matrix t
      (ReplicatedTarget.repeated vertex copies) (label.symm i))) (hbudget : cs.length ≤ r + m) :
    Certified label vertex (ReplicatedTarget.repeated vertex copies) cs := by
  refine ⟨ClassicalTarget.fresh label vertex hv hzero copies cs t hout hbudget,
    fun pre g post heq => ClassicalTarget.birth_cases label vertex hv hzero copies cs t hout hbudget pre post g heq, ?_, ?_⟩
  · intro a
    simpa only [recorder, Equiv.symm_apply_apply, RecorderVectors.target_recorder_row] using hout (recorder label a)
  · intro j
    simpa only [Equiv.symm_apply_apply, RecorderVectors.target_coordinate_row] using hout (label (.inl j))

theorem policy (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) (cs : List (AddGate n)) (h : Certified label vertex X cs) :
    RecorderRigidity.Policy label X cs := by
  intro pre g post heq
  rcases h.births pre g post heq with ho | ⟨v, hv⟩
  · exact Or.inl ho
  · exact Or.inr (fun a => by rw [hv, RecorderVectors.parity_recorder])

theorem coordinate_prefix (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) (cs : List (AddGate n)) (h : Certified label vertex X cs)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post) (j : Fin d) :
    runRows pre (standard n).x (label (.inl j)) = (standard n).x (label (.inl j)) :=
  RowRigidity.restored_initial_fixed cs h.fresh pre post heq _ (h.coordinates j)

theorem coordinate_not_target (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) (cs : List (AddGate n)) (h : Certified label vertex X cs)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post) (j : Fin d) :
    g.target ≠ label (.inl j) :=
  RowRigidity.restored_initial_not_target cs h.fresh pre post g heq _ (h.coordinates j)

theorem path_birth (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) (cs : List (AddGate n)) (h : Certified label vertex X cs)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post)
    (ht : g.target = pathWire label) :
    ∃ v : Fin m, newRow pre g (standard n).x = parity label (vertex v.succ) := by
  rcases h.births pre g post heq with ⟨a, ha⟩ | hv
  · have hh := RecorderRigidity.output_birth_own label X cs h.fresh h.outputs pre post g heq a ha
    have he := label.injective (ht.symm.trans hh)
    simp at he
  · exact hv

theorem parity_target_path (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) (cs : List (AddGate n)) (h : Certified label vertex X cs)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post)
    (v : Fin d → F) (hv : newRow pre g (standard n).x = parity label v) : g.target = pathWire label := by
  obtain ⟨w, hw⟩ := label.surjective g.target
  rcases w with j | (u | a)
  · exact False.elim (coordinate_not_target label vertex X cs h pre post g heq j hw.symm)
  · cases u
    exact hw.symm
  · have ho := RecorderRigidity.recorder_birth_output label X cs h.fresh (policy label vertex X cs h)
      h.outputs pre post g heq a hw.symm
    exact False.elim (RecorderVectors.parity_ne_output label X v a (hv.symm.trans ho))

/-- A path update cannot use a recorder as control: its private coordinate
would then occur in the data-only updated path row. -/
theorem path_control_coordinate (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) (cs : List (AddGate n)) (h : Certified label vertex X cs)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post)
    (ht : g.target = pathWire label) : ∃ j : Fin d, g.control = label (.inl j) := by
  obtain ⟨w, hw⟩ := label.surjective g.control
  rcases w with j | (u | a)
  · exact ⟨j, hw.symm⟩
  · cases u
    exact False.elim (g.distinct (hw.symm.trans ht.symm))
  · have hp := policy label vertex X cs h
    have hzero := RecorderRigidity.private_column label X cs h.fresh hp h.outputs pre (g :: post) heq a
      (pathWire label) (by simp [pathWire, recorder])
    have hone := RecorderRigidity.recorder_coordinate label X cs h.fresh hp h.outputs pre (g :: post) heq a
    obtain ⟨v, hv⟩ := path_birth label vertex X cs h pre post g heq ht
    have hz : runRows pre (standard n).x g.target (recorder label a, false) = 0 := by simpa only [ht] using hzero
    have ho : runRows pre (standard n).x g.control (recorder label a, false) = 1 := by simpa only [recorder, hw] using hone
    have he' : runRows pre (standard n).x g.target (recorder label a, false) +
        runRows pre (standard n).x g.control (recorder label a, false) = 0 := by
      simpa only [RowHistory.newRow_eq, Pi.add_apply, RecorderVectors.parity_recorder] using congrFun hv (recorder label a, false)
    rw [hz, ho] at he'
    norm_num at he'

theorem path_step (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) (cs : List (AddGate n)) (h : Certified label vertex X cs)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post)
    (ht : g.target = pathWire label) : ∃ j : Fin d,
    newRow pre g (standard n).x = runRows pre (standard n).x (pathWire label) + (standard n).x (label (.inl j)) := by
  obtain ⟨j, hj⟩ := path_control_coordinate label vertex X cs h pre post g heq ht
  refine ⟨j, ?_⟩
  rw [RowHistory.newRow_eq, ht, hj, coordinate_prefix label vertex X cs h pre (g :: post) heq j]

theorem parity_location (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) (cs : List (AddGate n)) (h : Certified label vertex X cs)
    (pre post : List (AddGate n)) (heq : cs = pre ++ post) (i : Fin n) (v : Fin d → F)
    (hv : runRows pre (standard n).x i = parity label v) : i = pathWire label := by
  obtain ⟨w, rfl⟩ := label.surjective i
  rcases w with j | (u | a)
  · have hc := coordinate_prefix label vertex X cs h pre post heq j
    rw [hv] at hc
    have hh := congrFun hc (pathWire label, false)
    simp [pathWire, RecorderVectors.parity_path, RecorderVectors.basis_apply] at hh
  · cases u
    rfl
  · have hh := RecorderRigidity.recorder_coordinate label X cs h.fresh (policy label vertex X cs h)
      h.outputs pre post heq a
    change runRows pre (standard n).x (label (.inr (.inr a))) (recorder label a, false) = 1 at hh
    rw [hv, RecorderVectors.parity_recorder] at hh
    norm_num at hh

end CliffordSynthesis.PathRows
