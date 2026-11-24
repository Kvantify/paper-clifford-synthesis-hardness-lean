/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.FreeLayers
public import CliffordSynthesis.StandardSpace

/-!
# Full Synthesis Columns

The symplectic pairings of the input columns under H, S and CNOT.
-/

@[expose] public section

namespace CliffordSynthesis.Circuit

open Planes (F)
open LocalChart (bit)
open FreeLayers (pair)

variable {n : Nat}

/-- Contribution of one wire to the symplectic pairing of two columns. -/
def wirePairing (u v : Bool × Bool) : F := bit u.1 * bit v.2 + bit u.2 * bit v.1

def columnPairing (a : Tableau n) (p q : Fin n × Bool) : F :=
  ∑ i, wirePairing (pair a i p) (pair a i q)

def ColumnsSymplectic (a : Tableau n) : Prop :=
  ∀ p q, columnPairing a p q = if p.1 = q.1 ∧ p.2 ≠ q.2 then 1 else 0

private theorem pairing_H :
    ∀ u v : Bool × Bool, wirePairing (u.2, u.1) (v.2, v.1) = wirePairing u v := by decide

private theorem pairing_S :
    ∀ u v : Bool × Bool,
      wirePairing (u.1, u.2 ^^ u.1) (v.1, v.2 ^^ v.1) = wirePairing u v := by decide

private theorem pairing_CX :
    ∀ uc vc ut vt : Bool × Bool,
      wirePairing (uc.1, uc.2 ^^ ut.2) (vc.1, vc.2 ^^ vt.2) +
        wirePairing (ut.1 ^^ uc.1, ut.2) (vt.1 ^^ vc.1, vt.2) =
      wirePairing uc vc + wirePairing ut vt := by decide

theorem columnsSymplectic_identity (n : Nat) : ColumnsSymplectic (identity n) := by
  rintro ⟨p, s⟩ ⟨q, t⟩
  unfold columnPairing
  rw [Finset.sum_eq_single p]
  · by_cases hpq : p = q <;> cases s <;> cases t <;>
      simp [pair, identity, wirePairing, bit, hpq]
  · intro i _ hip
    simp [pair, identity, wirePairing, bit, hip]
  · simp

theorem columnPairing_gate (a : Tableau n) (g : Gate n) (p q : Fin n × Bool) :
    columnPairing (applyGate g a) p q = columnPairing a p q := by
  unfold columnPairing
  cases g with
  | H c =>
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = c
      · subst i
        simpa [applyGate, pair, hadamard] using pairing_H (pair a c p) (pair a c q)
      · simp [applyGate, pair, hadamard, hi]
  | S c =>
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = c
      · subst i
        simpa [applyGate, pair, phase] using pairing_S (pair a c p) (pair a c q)
      · simp [applyGate, pair, phase, hi]
  | CX c t hct =>
      let f := fun i => wirePairing (pair (cnot c t a) i p) (pair (cnot c t a) i q)
      let h := fun i => wirePairing (pair a i p) (pair a i q)
      change (∑ i, f i) = ∑ i, h i
      have hm : c ∈ (Finset.univ : Finset (Fin n)).erase t := by simp [hct]
      rw [← Finset.sum_erase_add _ f (Finset.mem_univ t), ← Finset.sum_erase_add _ h (Finset.mem_univ t),
        ← Finset.sum_erase_add _ f hm, ← Finset.sum_erase_add _ h hm, add_assoc, add_assoc]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hic := (Finset.mem_erase.mp hi).1
        have hit := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        simp [f, h, pair, cnot, hic, hit]
      · simpa [f, h, pair, cnot, hct, Ne.symm hct] using
          pairing_CX (pair a c p) (pair a c q) (pair a t p) (pair a t q)

theorem ColumnsSymplectic.run {a : Tableau n} (h : ColumnsSymplectic a) (gs : List (Gate n)) :
    ColumnsSymplectic (run gs a) := by
  induction gs generalizing a with
  | nil => exact h
  | cons g gs ih =>
      apply ih
      intro p q
      rw [columnPairing_gate, h]

end CliffordSynthesis.Circuit
