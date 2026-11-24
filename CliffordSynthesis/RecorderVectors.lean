/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.RowExtraction
public import CliffordSynthesis.Target

/-!
# Recorder Vectors

Concrete coordinate, path, and recorder vectors, transported into the
original circuit's canonical space by a bijective physical wire labelling.
-/

@[expose] public section

namespace CliffordSynthesis.RecorderVectors

open Planes (F)
open StandardSpace (Space standard)
open Target (Wire)

variable {d r n : Nat}

def embed (label : Wire d r ≃ Fin n) (v : Wire d r → F) : Space n :=
  fun p => if p.2 then 0 else v (label.symm p.1)

def rawParity (v : Fin d → F) : Wire d r → F :=
  fun w => Sum.casesOn w (fun j => v j)
    (fun w' => Sum.casesOn w' (fun _ => 1) (fun _ => 0))

def parity (label : Wire d r ≃ Fin n) (v : Fin d → F) : Space n :=
  embed label (rawParity v)

def recorder (label : Wire d r ≃ Fin n) (a : Fin r) : Fin n := label (.inr (.inr a))

def output (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F) (a : Fin r) : Space n :=
  (standard n).x (recorder label a) + parity label (X a)

theorem embed_apply (label : Wire d r ≃ Fin n) (v : Wire d r → F) (w : Wire d r) :
    embed label v (label w, false) = v w := by simp [embed]

theorem embed_injective (label : Wire d r ≃ Fin n) : Function.Injective (embed label) := by
  intro u v huv
  funext w
  simpa only [embed_apply] using congrFun huv (label w, false)

theorem basis_apply (label : Wire d r ≃ Fin n) (i j : Wire d r) :
    (standard n).x (label i) (label j, false) = if j = i then 1 else 0 := by
  simp [standard, Pi.single_apply, Prod.mk.injEq]

theorem parity_coordinate (label : Wire d r ≃ Fin n) (v : Fin d → F) (j : Fin d) :
    parity label v (label (.inl j), false) = v j := by simp [parity, embed_apply, rawParity]

theorem parity_path (label : Wire d r ≃ Fin n) (v : Fin d → F) :
    parity label v (label (.inr (.inl ())), false) = 1 := by simp [parity, embed_apply, rawParity]

theorem parity_recorder (label : Wire d r ≃ Fin n) (v : Fin d → F) (a : Fin r) :
    parity label v (recorder label a, false) = 0 := by simp [recorder, parity, embed_apply, rawParity]

theorem parity_injective (label : Wire d r ≃ Fin n) : Function.Injective (parity label) := by
  intro u v huv
  funext j
  simpa only [parity_coordinate] using congrFun huv (label (.inl j), false)

theorem recorder_injective (label : Wire d r ≃ Fin n) : Function.Injective (recorder label) := by
  intro a b hab
  exact Sum.inr.inj (Sum.inr.inj (label.injective hab))

theorem output_recorder (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F) (a b : Fin r) :
    output label X a (recorder label b, false) = if b = a then 1 else 0 := by
  simp only [output, Pi.add_apply, parity_recorder, add_zero]
  simp [recorder, basis_apply]

theorem output_path (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F) (a : Fin r) :
    output label X a (label (.inr (.inl ())), false) = 1 := by
  simp [output, Pi.add_apply, parity_path, recorder, basis_apply]

theorem output_injective (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F) :
    Function.Injective (output label X) := by
  intro a b hab
  by_contra h
  have hh := congrFun hab (recorder label a, false)
  simp [output_recorder, h] at hh

theorem output_not_initial (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (a : Fin r) (i : Fin n) : (standard n).x i ≠ output label X a := by
  intro h
  obtain ⟨w, rfl⟩ := label.surjective i
  by_cases hw : w = .inr (.inr a)
  · subst w
    have hh := congrFun h (label (.inr (.inl ())), false)
    simp [basis_apply, output_path] at hh
  · have hh := congrFun h (recorder label a, false)
    rw [output_recorder] at hh
    simp [recorder, basis_apply, Ne.symm hw] at hh

theorem parity_ne_output (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (v : Fin d → F) (a : Fin r) : parity label v ≠ output label X a := by
  intro h
  have hh := congrFun h (recorder label a, false)
  simp [parity_recorder, output_recorder] at hh

theorem zero_parity (label : Wire d r ≃ Fin n) :
    parity label (0 : Fin d → F) = (standard n).x (label (.inr (.inl ()))) := by
  funext p
  rcases p with ⟨i, b⟩
  obtain ⟨w, rfl⟩ := label.surjective i
  cases b
  · rcases w with w | (w | w) <;> simp [parity, embed_apply, rawParity, basis_apply]
  · simp [parity, embed, standard]

theorem nonzero_parity_not_initial (label : Wire d r ≃ Fin n) (v : Fin d → F) (hv : v ≠ 0)
    (i : Fin n) : (standard n).x i ≠ parity label v := by
  intro h
  obtain ⟨w, rfl⟩ := label.surjective i
  have hh := congrFun h (label (.inr (.inl ())), false)
  have hw : w = .inr (.inl ()) := by
    by_contra hw
    simp [basis_apply, Ne.symm hw, parity_path] at hh
  subst w
  exact hv (parity_injective label (h.symm.trans (zero_parity label).symm))

theorem parity_mem (label : Wire d r ≃ Fin n) (v : Fin d → F) :
    parity label v ∈ StandardSpace.initialW n := by
  simp [StandardSpace.initialW_mem, parity, embed]

theorem output_mem (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F) (a : Fin r) :
    output label X a ∈ StandardSpace.initialW n := by
  apply Submodule.add_mem
  · simp [StandardSpace.initialW_mem, standard]
  · exact parity_mem label (X a)

/-- The concrete recorder output is precisely the corresponding row of A. -/
theorem target_recorder_row (label : Wire d r ≃ Fin n) (t : Fin d → F)
    (X : Fin r → Fin d → F) (a : Fin r) :
    embed label (Target.matrix t X (.inr (.inr a))) = output label X a := by
  funext p
  rcases p with ⟨i, b⟩
  obtain ⟨w, rfl⟩ := label.surjective i
  cases b
  · rcases w with w | (w | w) <;>
      simp [embed_apply, Target.matrix, Target.offset, Matrix.one_apply, output,
        Pi.add_apply, parity, embed_apply, rawParity, recorder, basis_apply, eq_comm]
  · simp [embed, output, parity, standard]

theorem target_coordinate_row (label : Wire d r ≃ Fin n) (t : Fin d → F)
    (X : Fin r → Fin d → F) (j : Fin d) :
    embed label (Target.matrix t X (.inl j)) = (standard n).x (label (.inl j)) := by
  funext p
  rcases p with ⟨i, b⟩
  obtain ⟨w, rfl⟩ := label.surjective i
  cases b
  · rcases w with w | (w | w) <;>
      simp [embed_apply, Target.matrix, Target.offset, Matrix.one_apply, basis_apply, eq_comm]
  · simp [embed, standard]

theorem target_path_row (label : Wire d r ≃ Fin n) (t : Fin d → F)
    (X : Fin r → Fin d → F) :
    embed label (Target.matrix t X (.inr (.inl ()))) = parity label t := by
  funext p
  rcases p with ⟨i, b⟩
  obtain ⟨w, rfl⟩ := label.surjective i
  cases b
  · rcases w with w | (w | w) <;>
      simp [embed_apply, Target.matrix, Target.offset, parity, rawParity]
  · simp [embed, parity]

end CliffordSynthesis.RecorderVectors
