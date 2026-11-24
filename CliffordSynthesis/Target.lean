/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic

/-!
# Target

The concrete coordinate/path/recorder target and its symplectic lift.
The arbitrary matrix X permits any replication of vertex rows.
-/

@[expose] public section

namespace CliffordSynthesis.Target

open Matrix

abbrev F := ZMod 2
abbrev Wire (d r : Nat) := Fin d ⊕ (Unit ⊕ Fin r)
abbrev Mat (d r : Nat) := Matrix (Wire d r) (Wire d r) F

/-- A-I in coordinate, path, recorder order. -/
def offset {d r : Nat} (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) : Mat d r
  | .inl _, _ => 0
  | .inr (.inl _), .inl j => t j
  | .inr (.inl _), .inr _ => 0
  | .inr (.inr a), .inl j => X a j
  | .inr (.inr _), .inr (.inl _) => 1
  | .inr (.inr _), .inr (.inr _) => 0

def squareOffset {d r : Nat} (t : Fin d → F) : Mat d r
  | .inl _, _ => 0
  | .inr (.inl _), _ => 0
  | .inr (.inr _), .inl j => t j
  | .inr (.inr _), .inr _ => 0

def matrix {d r : Nat} (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) : Mat d r :=
  1 + offset t X

def inverse {d r : Nat} (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F) : Mat d r :=
  1 + offset t X + squareOffset t

variable {d r : Nat} (t : Fin d → F) (X : Matrix (Fin r) (Fin d) F)

theorem offset_sq : offset t X ^ 2 = squareOffset t := by
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [pow_two, Matrix.mul_apply, offset, squareOffset, Fintype.sum_sum_type]

theorem offset_cube : offset t X ^ 3 = 0 := by
  rw [pow_succ, offset_sq]
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [Matrix.mul_apply, offset, squareOffset, Fintype.sum_sum_type]

theorem nilpotent_target : (matrix t X - 1) ^ 3 = 0 := by
  simpa [matrix] using offset_cube t X

private theorem inverse_polynomial (D : Mat d r) (hD : D ^ 3 = 0) :
    (1 + D) * (1 + D + D ^ 2) = 1 := by
  have h : (1 + D) * (1 + D + D ^ 2) = 1 + (D + D) + (D ^ 2 + D ^ 2) + D ^ 3 := by
    noncomm_ring
  have hz (M : Mat d r) : M + M = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero (M i j)
  rw [h, hD, hz, hz]
  simp

theorem matrix_mul_inverse : matrix t X * inverse t X = 1 := by
  unfold matrix inverse
  rw [← offset_sq t X]
  exact inverse_polynomial _ (offset_cube t X)

theorem inverse_mul_matrix : inverse t X * matrix t X = 1 := by
  exact (mul_eq_one_comm).mp (matrix_mul_inverse t X)

/-- The explicit inverse equals Mathlib's nonsingular matrix inverse. -/
theorem inverse_eq : inverse t X = (matrix t X)⁻¹ := by
  exact (Matrix.inv_eq_right_inv (matrix_mul_inverse t X)).symm

/-- The target is an element of GL, with a directly computable inverse. -/
def unit : (Mat d r)ˣ where
  val := matrix t X
  inv := inverse t X
  val_inv := matrix_mul_inverse t X
  inv_val := inverse_mul_matrix t X

/-- rho(A) = diag(A,A^(-T)), in X/Z order. -/
def lift : Matrix (Wire d r ⊕ Wire d r) (Wire d r ⊕ Wire d r) F :=
  Matrix.fromBlocks (matrix t X) 0 0 (inverse t X)ᵀ

theorem lift_symplectic : lift t X ∈ Matrix.symplecticGroup (Wire d r) F := by
  rw [lift, SymplecticGroup.fromBlocks_mem_iff]
  simp only [transpose_zero, Matrix.mul_zero, Matrix.zero_mul, sub_zero, and_self_left]
  rw [← Matrix.transpose_mul, inverse_mul_matrix, Matrix.transpose_one]
  simp

/-- Numeric order of physical wires, with coordinates first and recorders last. -/
def position : Wire d r → Nat
  | .inl i => i.val
  | .inr (.inl _) => d
  | .inr (.inr a) => d + 1 + a.val

theorem diagonal (i : Wire d r) : matrix t X i i = 1 := by
  rcases i with i | (i | i) <;> simp [matrix, offset]

theorem lower_triangular (i j : Wire d r) (h : position i < position j) :
    matrix t X i j = 0 := by
  have hij : i ≠ j := by intro he; subst j; exact Nat.lt_irrefl _ h
  simp only [matrix, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add]
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [offset]
  all_goals simp only [position] at h
  all_goals omega

end CliffordSynthesis.Target
