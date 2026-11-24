/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.TwoQubitAlgebra
public import CliffordSynthesis.StandardSpace

/-!
# Two Qubit Symplectic

The finite validity test is exactly the symplectic-tableau
predicate, so the normal form covers every two-qubit binary symplectic map.
-/

@[expose] public section

namespace CliffordSynthesis.TwoQubit

open Planes (F)
open LocalChart (bit)

private theorem bit_and (a b : Bool) : bit (a && b) = bit a * bit b := by
  cases a <;> cases b <;> decide

private theorem bit_eq_one (b : Bool) : bit b = 1 ↔ b = true := by cases b <;> decide
private theorem bit_eq_zero (b : Bool) : bit b = 0 ↔ b = false := by cases b <;> decide

def fieldRow (v : BitVec 4) : StandardSpace.Space 2 :=
  fun p => bit (v.getLsbD (2 * p.1.val + p.2.toNat))

def matrixRows (p : Matrix) : SymplecticCircuit.Rows 2 (StandardSpace.Space 2) where
  x i := fieldRow (row p (2 * i.val))
  z i := fieldRow (row p (2 * i.val + 1))

theorem fieldRow_form (u v : BitVec 4) :
    StandardSpace.form 2 (fieldRow u) (fieldRow v) = bit (gram u v) := by
  simp [StandardSpace.form_apply, Fin.sum_univ_two, fieldRow, gram, LocalChart.bit_xor, bit_and, add_assoc]

theorem gram_self : ∀ u : BitVec 4, gram u u = false := by decide
theorem gram_symm : ∀ u v : BitVec 4, gram u v = gram v u := by decide

/-- The six Boolean checks are equivalent to M J Mᵀ = J, expressed using the
same bilinear form and row conventions as the rest of the development. -/
theorem valid_iff_symplectic (p : Matrix) : valid p = true ↔
    SymplecticCircuit.IsSymplectic (StandardSpace.form 2) (matrixRows p) := by
  constructor
  · intro h
    simp only [valid, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨h01, h23⟩, h02⟩, h03⟩, h12⟩, h13⟩ := h
    have h10 := (gram_symm (row p 1) (row p 0)).trans h01
    have h32 := (gram_symm (row p 3) (row p 2)).trans h23
    have h20 := (gram_symm (row p 2) (row p 0)).trans h02
    have h30 := (gram_symm (row p 3) (row p 0)).trans h03
    have h21 := (gram_symm (row p 2) (row p 1)).trans h12
    have h31 := (gram_symm (row p 3) (row p 1)).trans h13
    constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [matrixRows, fieldRow_form, gram_self, h01, h23, h02, h03, h12, h13,
        h10, h32, h20, h30, h21, h31, bit]
  · intro h
    have h01 := h.xz 0 0
    have h23 := h.xz 1 1
    have h02 := h.xx 0 1
    have h03 := h.xz 0 1
    have h12 := h.zx 0 1
    have h13 := h.zz 0 1
    simp only [matrixRows, fieldRow_form, Fin.val_zero, Fin.val_one, mul_zero,
      mul_one, zero_add, Nat.reduceAdd, ite_true, bit_eq_one, bit_eq_zero] at h01 h23 h02 h03 h12 h13
    simp_all [valid, bit_eq_zero]

end CliffordSynthesis.TwoQubit
