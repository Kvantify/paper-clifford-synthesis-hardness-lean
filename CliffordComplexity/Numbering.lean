/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Nodup
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Numbering

Finite numberings with an initial interval of natural labels and elementary facts about
the position of each element.
-/

@[expose] public section

namespace CliffordComplexity

/-- An enumeration of a finite type with positions starting at zero. -/
structure Numbering (α : Type*) where
  size : Nat
  equivFin : α ≃ Fin size

namespace Numbering
variable {α β : Type*}

/-- The natural position assigned to an element by the numbering. -/
def num (N : Numbering α) (a : α) : Nat := (N.equivFin a).val

theorem num_lt (N : Numbering α) (a : α) : N.num a < N.size := (N.equivFin a).isLt

theorem num_inj (N : Numbering α) : Function.Injective N.num :=
  fun _ _ h => N.equivFin.injective (Fin.ext h)

theorem num_surj (N : Numbering α) (i : Nat) (hi : i < N.size) : ∃ a, N.num a = i := by
  obtain ⟨a, ha⟩ := N.equivFin.surjective ⟨i, hi⟩
  exact ⟨a, congrArg Fin.val ha⟩

/-- Use the increasing order of the canonical finite interval. -/
def fin (n : Nat) : Numbering (Fin n) := ⟨n, Equiv.refl _⟩
/-- Number two Boolean values using the standard equivalence with `Fin 2`. -/
def bool : Numbering Bool := ⟨2, finTwoEquiv.symm⟩

/-- Number the left summand first, followed by the right summand. -/
def sum (A : Numbering α) (B : Numbering β) : Numbering (α ⊕ β) :=
  ⟨A.size + B.size, (Equiv.sumCongr A.equivFin B.equivFin).trans finSumFinEquiv⟩

/-- Number the product in lexicographic order from the two numberings. -/
def prod (A : Numbering α) (B : Numbering β) : Numbering (α × β) := by
  let e := (Equiv.prodCongr A.equivFin B.equivFin).trans finProdFinEquiv
  let position (p : α × β) : Fin (A.size * B.size) :=
    ⟨A.num p.1 * B.size + B.num p.2, by
      simpa [e, num, Nat.mul_comm, Nat.add_comm] using (e p).isLt⟩
  have he (p : α × β) : position p = e p := by
    apply Fin.ext
    simp [position, e, num, Nat.mul_comm, Nat.add_comm]
  exact ⟨_, ⟨position, e.symm, fun p => by rw [he, Equiv.symm_apply_apply],
    fun p => by rw [he, Equiv.apply_symm_apply]⟩⟩

@[simp] theorem fin_num {n : Nat} (i : Fin n) : (fin n).num i = i.val := rfl
@[simp] theorem fin_size (n : Nat) : (fin n).size = n := rfl
@[simp] theorem bool_num (b : Bool) : bool.num b = b.toNat := by cases b <;> rfl
@[simp] theorem bool_size : bool.size = 2 := rfl
@[simp] theorem sum_num_inl (A : Numbering α) (B : Numbering β) (a : α) :
    (A.sum B).num (.inl a) = A.num a := rfl
@[simp] theorem sum_num_inr (A : Numbering α) (B : Numbering β) (b : β) :
    (A.sum B).num (.inr b) = A.size + B.num b := rfl
@[simp] theorem sum_size (A : Numbering α) (B : Numbering β) :
    (A.sum B).size = A.size + B.size := rfl
@[simp] theorem prod_num (A : Numbering α) (B : Numbering β) (a : α) (b : β) :
    (A.prod B).num (a, b) = A.num a * B.size + B.num b := rfl
@[simp] theorem prod_size (A : Numbering α) (B : Numbering β) :
    (A.prod B).size = A.size * B.size := rfl
@[simp] theorem equivFin_val (N : Numbering α) (a : α) : (N.equivFin a).val = N.num a := rfl

theorem num_pair_inj (N : Numbering α) :
    Function.Injective (fun p : α × α => (N.num p.1, N.num p.2)) := by
  grind [Function.Injective, N.num_inj]

theorem mem_map_num_pair (N : Numbering α) {L : List (α × α)} {u w : α} :
    (N.num u, N.num w) ∈ L.map (fun p => (N.num p.1, N.num p.2)) ↔ (u, w) ∈ L :=
  List.mem_map_of_injective N.num_pair_inj (a := (u, w)) (l := L)

end Numbering
end CliffordComplexity
