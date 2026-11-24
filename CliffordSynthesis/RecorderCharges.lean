/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.BirthOccurrences

/-!
# Recorder Charges

The two injections into unselected appearances used in the missing-parity
argument. `MissingParity.count_bound` proves that these two classes and the
exceptional appearances cover all recorders requesting a missing parity.
-/

@[expose] public section

namespace CliffordSynthesis.RecorderCharges

open Planes (F)
open SymplecticCircuit (Rows)
open BirthOccurrences (Occurrence occurrences atTime)

variable {V : Type*} [AddCommGroup V] [Module F V] {n r : Nat}

attribute [local instance] Classical.propDecidable

def designated (recorder : Fin r → Fin n) (time : Fin r → Nat) : Finset (Occurrence n) :=
  Finset.univ.image (fun j => (time j, recorder j))

theorem designated_card (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (time : Fin r → Nat) : (designated recorder time).card = r := by
  rw [designated, Finset.card_image_of_injective _ (fun i j h => hr (congrArg Prod.snd h))]
  simp

noncomputable def undesignated (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (recorder : Fin r → Fin n) (time : Fin r → Nat) : Finset (Occurrence n) :=
  occurrences W gs a \ designated recorder time

theorem undesignated_card (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (recorder : Fin r → Fin n) (hr : Function.Injective recorder) (time : Fin r → Nat)
    (hd : ∀ j, (time j, recorder j) ∈ occurrences W gs a) :
    (undesignated W gs a recorder time).card = CircuitLedger.totalBirths W gs a - r := by
  have hsub : designated recorder time ⊆ occurrences W gs a := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact hd j
  rw [undesignated, Finset.card_sdiff_of_subset hsub, BirthOccurrences.occurrences_card,
    designated_card recorder hr time]

noncomputable def earlier (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (recorder : Fin r → Fin n) (time : Fin r → Nat) : Finset (Fin r) :=
  Finset.univ.filter (fun j => ∃ k, k < time j ∧ (k, recorder j) ∈ occurrences W gs a)

private theorem earlier_not_designated (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (time : Fin r → Nat) (j : Fin r) (k : Nat) (hk : k < time j) :
    (k, recorder j) ∉ designated recorder time := by
  intro hp
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
  have hij : i = j := hr (congrArg Prod.snd hi)
  subst i
  have ht := congrArg Prod.fst hi
  simp only at ht
  omega

/-- Distinct recorder wires with earlier births inject into undesignated
occurrences, giving the first E term in the missing-parity bound. -/
theorem earlier_count_le_excess (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (recorder : Fin r → Fin n) (hr : Function.Injective recorder) (time : Fin r → Nat)
    (hd : ∀ j, (time j, recorder j) ∈ occurrences W gs a) :
    (earlier W gs a recorder time).card ≤ CircuitLedger.totalBirths W gs a - r := by
  classical
  have hh (j : ↥(earlier W gs a recorder time)) :
      ∃ k, k < time j ∧ (k, recorder j) ∈ occurrences W gs a := by
    simpa [earlier] using j.property
  choose k hk hmem using hh
  let f : ↥(earlier W gs a recorder time) → ↥(undesignated W gs a recorder time) := fun j =>
    ⟨(k j, recorder j), Finset.mem_sdiff.mpr
      ⟨hmem j, earlier_not_designated recorder hr time j (k j) (hk j)⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact hr (congrArg (fun p : ↥(undesignated W gs a recorder time) => p.val.2) hij)
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, undesignated_card W gs a recorder hr time hd] using hc

noncomputable def wrongWire (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (recorder : Fin r → Fin n) (output : Fin r → V) : Finset (Fin r) :=
  Finset.univ.filter (fun j => ∃ p ∈ occurrences W gs a,
    atTime W gs a (p.1 + 1) p.2 = some (output j) ∧ p.2 ≠ recorder j)

private theorem wrong_not_designated (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (recorder : Fin r → Fin n) (output : Fin r → V) (ho : Function.Injective output)
    (time : Fin r → Nat) (hdv : ∀ j, atTime W gs a (time j + 1) (recorder j) = some (output j))
    (j : Fin r) (p : Occurrence n)
    (hv : atTime W gs a (p.1 + 1) p.2 = some (output j)) (hw : p.2 ≠ recorder j) :
    p ∉ designated recorder time := by
  intro hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hji : j = i := ho (Option.some.inj (hv.symm.trans (hdv i)))
  exact hw (by simp [hji])

/-- Distinct output vectors, even when born on arbitrary mixed wires, inject
into undesignated occurrences. This is the second E term in the missing-parity bound. -/
theorem wrong_wire_count_le_excess (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (output : Fin r → V) (ho : Function.Injective output) (time : Fin r → Nat)
    (hd : ∀ j, (time j, recorder j) ∈ occurrences W gs a)
    (hdv : ∀ j, atTime W gs a (time j + 1) (recorder j) = some (output j)) :
    (wrongWire W gs a recorder output).card ≤ CircuitLedger.totalBirths W gs a - r := by
  classical
  have hh (j : ↥(wrongWire W gs a recorder output)) :
      ∃ p ∈ occurrences W gs a, atTime W gs a (p.1 + 1) p.2 = some (output j) ∧ p.2 ≠ recorder j := by
    simpa [wrongWire] using j.property
  choose p hmem hvalue hwire using hh
  let f : ↥(wrongWire W gs a recorder output) → ↥(undesignated W gs a recorder time) := fun j =>
    ⟨p j, Finset.mem_sdiff.mpr
      ⟨hmem j, wrong_not_designated W gs a recorder output ho time hdv j (p j) (hvalue j) (hwire j)⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hp : p i = p j := congrArg Subtype.val hij
    have hv := hvalue i
    rw [hp] at hv
    apply Subtype.ext
    exact ho (Option.some.inj (hv.symm.trans (hvalue j)))
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, undesignated_card W gs a recorder hr time hd] using hc

end CliffordSynthesis.RecorderCharges
