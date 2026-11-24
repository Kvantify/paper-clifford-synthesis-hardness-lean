/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.RecorderVectors

/-!
# Displaced Algebra

Algebra for recorder outputs on arbitrary final wires.
-/

@[expose] public section

namespace CliffordSynthesis.DisplacedAlgebra

open Planes (F)
open StandardSpace (Space standard)
open RecorderVectors (parity recorder output)
open Target (Wire)

variable {d r n : Nat}

@[simp] theorem basis_at (i j : Fin n) :
    (standard n).x i (j, false) = if j = i then 1 else 0 := by
  simp [standard, Pi.single_apply, Prod.mk.injEq]

@[simp] theorem double (v : Space n) : v + v = 0 := by
  ext p
  exact CharTwo.add_self_eq_zero (v p)

theorem basis_ne_zero (i : Fin n) : (standard n).x i ≠ 0 := by
  intro h
  have hh := congrFun h (i, false)
  simp at hh

/-- Adding a single initial basis vector to a recorder output cannot yield
another recorder output, even when the two data parities differ. -/
theorem shifted_ne_output (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (a b : Fin r) (i : Fin n) :
    output label X a + (standard n).x i ≠ output label X b := by
  intro h
  by_cases hab : a = b
  · subst b
    have hz : (standard n).x i = 0 := add_left_cancel (h.trans (add_zero _).symm)
    exact basis_ne_zero i hz
  · have ha := congrFun h (recorder label a, false)
    have hb := congrFun h (recorder label b, false)
    simp only [Pi.add_apply, RecorderVectors.output_recorder, basis_at] at ha hb
    have hi : recorder label a = i := by
      by_contra hi
      simp [hab, hi] at ha
    have hba : recorder label b ≠ i := by
      rw [← hi]
      exact fun h => hab ((RecorderVectors.recorder_injective label h).symm)
    simp [Ne.symm hab, hba] at hb

/-- If the data parity is not initial, neither is an output with one initial
basis vector added. -/
theorem shifted_not_initial (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (a : Fin r) (i : Fin n)
    (hf : ∀ j, (standard n).x j ≠ parity label (X a)) :
    ∀ j, (standard n).x j ≠ output label X a + (standard n).x i := by
  intro j h
  by_cases hi : i = recorder label a
  · subst i
    have hc : output label X a + (standard n).x (recorder label a) = parity label (X a) := by
      rw [output, add_right_comm, double, zero_add]
    exact hf j (h.trans hc)
  · have ha := congrFun h (recorder label a, false)
    simp only [Pi.add_apply, RecorderVectors.output_recorder, basis_at] at ha
    have hj : j = recorder label a := by
      by_contra hj
      simp [Ne.symm hi, Ne.symm hj] at ha
    subst j
    have hc : parity label (X a) + (standard n).x i = 0 := by
      apply add_left_cancel (a := (standard n).x (recorder label a))
      simpa only [output, add_assoc, add_zero] using h.symm
    have hfi : (standard n).x i = parity label (X a) := by
      have hh := congrArg (fun v => v + (standard n).x i) hc
      simpa only [add_assoc, double, add_zero, zero_add] using hh.symm
    exact hf i hfi

/-- An eligible source is either the recorder output itself or that output
plus the basis vector of a different physical wire. -/
def Source (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (final : Fin r → Fin n) (a : Fin r) (b : Space n) : Prop :=
  b = output label X a ∨
    final a ≠ recorder label a ∧ b = output label X a + (standard n).x (final a)

theorem source_recorder (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (final : Fin r → Fin n) (a : Fin r) (b : Space n) (hb : Source label X final a b) :
    b (recorder label a, false) = 1 := by
  rcases hb with rfl | ⟨hi, rfl⟩
  · simp [RecorderVectors.output_recorder]
  · simp [Pi.add_apply, RecorderVectors.output_recorder, Ne.symm hi]

/-- Among recorders requesting a common parity, a fixed source can be charged
by at most the two recorder indices in its recorder-coordinate support. -/
theorem source_support (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (final : Fin r → Fin n) (a c : Fin r) (b : Space n)
    (ha : Source label X final a b) (hc : Source label X final c b) :
    recorder label c = recorder label a ∨ recorder label c = final a := by
  have hone := source_recorder label X final c b hc
  by_contra h
  push Not at h
  have hca : c ≠ a := fun hh => h.1 (congrArg (recorder label) hh)
  rcases ha with rfl | ⟨_, rfl⟩
  · simp [RecorderVectors.output_recorder, hca] at hone
  · simp [Pi.add_apply, RecorderVectors.output_recorder, hca, h.2] at hone

end CliffordSynthesis.DisplacedAlgebra
