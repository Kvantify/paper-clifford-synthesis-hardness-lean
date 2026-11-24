/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.RowHistory

/-!
# Classical Lift

A CNOT-only implementation of A implements its entire symplectic lift,
including the inverse-transpose Z block in the Boolean tableau.
-/

@[expose] public section

namespace CliffordSynthesis.ClassicalLift

open Matrix
open Planes (F)
open RowExtraction (AddGate runRows)
open RowHistory (asCircuit)
open StandardSpace (Space standard fieldRows)
open SymplecticCircuit (Rows IsSymplectic)
open RecorderVectors (embed)
open Target (Wire)

variable {d r n : Nat}

def zMatrix (label : Wire d r ≃ Fin n) (a : Rows n (Space n)) : Target.Mat d r :=
  fun i j => a.z (label i) (label j, true)

theorem matrix_z_inverse (label : Wire d r ≃ Fin n) (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F)
    (a : Rows n (Space n)) (ha : IsSymplectic (StandardSpace.form n) a)
    (hx : ∀ i, a.x i = embed label (Target.matrix t X (label.symm i))) :
    Target.matrix t X * (zMatrix label a)ᵀ = 1 := by
  ext i j
  calc
    (Target.matrix t X * (zMatrix label a)ᵀ) i j =
        ∑ k : Wire d r, Target.matrix t X i k * a.z (label j) (label k, true) := rfl
    _ = ∑ k : Fin n, (a.x (label i) (k, false) * a.z (label j) (k, true) +
        a.x (label i) (k, true) * a.z (label j) (k, false)) := by
      apply Fintype.sum_equiv label
      intro k
      simp [hx, embed]
    _ = if label i = label j then 1 else 0 := by
      rw [← StandardSpace.form_apply]
      exact ha.xz (label i) (label j)
    _ = (1 : Target.Mat d r) i j := by simp [Matrix.one_apply]

theorem z_inverse_transpose (label : Wire d r ≃ Fin n) (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F)
    (a : Rows n (Space n)) (ha : IsSymplectic (StandardSpace.form n) a)
    (hx : ∀ i, a.x i = embed label (Target.matrix t X (label.symm i))) (i j : Fin n) :
    a.z i (j, true) = Target.inverse t X (label.symm j) (label.symm i) := by
  have hz : (zMatrix label a)ᵀ = Target.inverse t X := by
    calc
      (zMatrix label a)ᵀ = (Target.inverse t X * Target.matrix t X) * (zMatrix label a)ᵀ := by
        rw [Target.inverse_mul_matrix, one_mul]
      _ = Target.inverse t X * (Target.matrix t X * (zMatrix label a)ᵀ) := mul_assoc _ _ _
      _ = Target.inverse t X := by rw [matrix_z_inverse label t X a ha hx, mul_one]
  have hh := congrFun (congrFun hz (label.symm j)) (label.symm i)
  simpa only [Matrix.transpose_apply, zMatrix, Equiv.apply_symm_apply] using hh

theorem run_z_zero (cs : List (AddGate n)) (a : Rows n (Space n))
    (hz : ∀ i j, a.z i (j, false) = 0) :
    ∀ i j, (SymplecticCircuit.run (asCircuit cs) a).z i (j, false) = 0 := by
  induction cs generalizing a with
  | nil => exact hz
  | cons g cs ih =>
    apply ih (SymplecticCircuit.CX g.control g.target a)
    intro i j
    simp [SymplecticCircuit.CX, ite_apply, Pi.add_apply, hz]

theorem bit_injective : Function.Injective LocalChart.bit := by decide

/-- Equality of classical X rows supplies equality of the complete Boolean
tableau for a CNOT-only circuit; the Z rows are proved, not assumed. -/
theorem same_target (label : Wire d r ≃ Fin n) (cs : List (AddGate n))
    (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F)
    (hx : ∀ i, runRows cs (standard n).x i = embed label (Target.matrix t X (label.symm i))) :
    Circuit.Same (Circuit.run (asCircuit cs) (Circuit.identity n)) (EncodedTarget.tableau label t X) := by
  have ha := SymplecticCircuit.run_symplectic (StandardSpace.form n) (asCircuit cs) _ (StandardSpace.standard_symplectic n)
  have hx' : ∀ i, (SymplecticCircuit.run (asCircuit cs) (standard n)).x i =
      embed label (Target.matrix t X (label.symm i)) := by simpa only [RowHistory.circuit_x] using hx
  have hz := z_inverse_transpose label t X _ ha hx'
  have hz0 := run_z_zero cs (standard n) (fun i j => by simp [standard])
  intro i p
  constructor
  · apply bit_injective
    change (fieldRows (Circuit.run (asCircuit cs) (Circuit.identity n))).x i p =
      (fieldRows (EncodedTarget.tableau label t X)).x i p
    rw [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity, hx' i]
    exact (congrFun (EncodedTarget.tableau_x label t X i) p).symm
  · apply bit_injective
    rcases p with ⟨j, b⟩
    change (fieldRows (Circuit.run (asCircuit cs) (Circuit.identity n))).z i (j, b) =
      (fieldRows (EncodedTarget.tableau label t X)).z i (j, b)
    rw [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity]
    refine Eq.trans ?_ (EncodedTarget.tableau_z label t X i j b).symm
    cases b
    · exact hz0 i j
    · exact hz i j

theorem synthesizes (label : Wire d r ≃ Fin n) (cs : List (AddGate n))
    (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F)
    (hx : ∀ i, runRows cs (standard n).x i = embed label (Target.matrix t X (label.symm i))) :
    Circuit.SynthesizesWithin (EncodedTarget.tableau label t X) cs.length :=
  ⟨asCircuit cs, Nat.le_of_eq (RowHistory.circuit_cost cs), same_target label cs t X hx⟩

end CliffordSynthesis.ClassicalLift
