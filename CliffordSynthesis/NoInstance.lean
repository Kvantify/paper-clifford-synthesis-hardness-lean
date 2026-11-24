/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.FreeLayers

/-!
# No Instance

The constant no-instance: three-qubit fanout at budget one.
-/

@[expose] public section

namespace CliffordSynthesis.NoInstance

open Circuit FreeLayers

variable {n : Nat}

def wires (g : Gate n) : Finset (Fin n) :=
  Gate.casesOn g (fun _ => ∅) (fun _ => ∅) (fun c t _ => {c, t})

def used (gs : List (Gate n)) : Finset (Fin n) :=
  List.rec ∅ (fun g _ s => wires g ∪ s) gs

theorem wires_card (g : Gate n) : (wires g).card ≤ 2 * paid g := by
  cases g <;> simp_all [wires, paid]

theorem used_card (gs : List (Gate n)) : (used gs).card ≤ 2 * cost gs := by
  induction gs with
  | nil => simp [used, cost]
  | cons g gs ih =>
    have hu := Finset.card_union_le (wires g) (used gs)
    have hg := wires_card g
    change (wires g ∪ used gs).card ≤ 2 * (paid g + cost gs)
    omega

def LocalAt (a : Tableau n) (i : Fin n) : Prop :=
  ∀ j : Fin n, i ≠ j → ∀ b : Bool, pair a i (j, b) = (false, false)

theorem identity_local (i : Fin n) : LocalAt (identity n) i := by
  intro j h b
  simp [pair, identity, h]

theorem gate_local (g : Gate n) (a : Tableau n) (i : Fin n)
    (hl : LocalAt a i) (hi : i ∉ wires g) : LocalAt (applyGate g a) i := by
  intro j hij b
  have hx : a.x i (j, b) = false := congrArg Prod.fst (hl j hij b)
  have hz : a.z i (j, b) = false := congrArg Prod.snd (hl j hij b)
  cases g with
  | H q => simp [applyGate, pair, hadamard, hx, hz]
  | S q => simp [applyGate, pair, phase, hx, hz]
  | CX c t hct =>
    have hi' : i ≠ c ∧ i ≠ t := by simpa [wires] using hi
    simp [applyGate, pair, cnot, hi'.1, hi'.2, hx, hz]

theorem run_local (gs : List (Gate n)) (a : Tableau n) (i : Fin n)
    (hl : LocalAt a i) (hi : i ∉ used gs) : LocalAt (run gs a) i := by
  induction gs generalizing a with
  | nil => exact hl
  | cons g gs ih =>
    have hi' : i ∉ wires g ∧ i ∉ used gs := by simpa [used] using hi
    exact ih (applyGate g a) (gate_local g a i hl hi'.1) hi'.2

theorem exists_unused (gs : List (Gate n)) (hn : 2 * cost gs < n) : ∃ i, i ∉ used gs := by
  by_contra h
  push Not at h
  have he : used gs = Finset.univ := Finset.eq_univ_of_forall h
  have hc := used_card gs
  rw [he, Finset.card_univ, Fintype.card_fin] at hc
  omega

def fanout : Tableau 3 := run [.CX 0 1 (by decide), .CX 0 2 (by decide)] (identity 3)

theorem fanout_nonlocal : ∀ i, ¬LocalAt fanout i := by unfold LocalAt; decide

theorem fanout_no_instance : ¬SynthesizesWithin fanout 1 := by
  rintro ⟨gs, hcost, hsame⟩
  obtain ⟨i, hi⟩ := exists_unused gs (by omega)
  have hl := run_local gs (identity 3) i (identity_local i) hi
  have he : run gs (identity 3) = fanout := tableau_ext (fun i p => Prod.ext (hsame i p).1 (hsame i p).2)
  rw [he] at hl
  exact fanout_nonlocal i hl

end CliffordSynthesis.NoInstance
