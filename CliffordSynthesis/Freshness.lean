/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Saturation

/-!
# Freshness

Global first appearances and the counting argument which forces freshness
when distinct required noninitial vectors exhaust the circuit's birth budget.
-/

public section

namespace CliffordSynthesis.Freshness

open Planes (F)
open SymplecticCircuit (Rows run)
open Observation (visible)
open BirthOccurrences (Occurrence occurrences atTime)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

theorem first_birth (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V) (q : V)
    (hi : ∀ i, visible W a i ≠ some q)
    (hv : ∃ s ≤ gs.length, ∃ i, atTime W gs a s i = some q) :
    ∃ p ∈ occurrences W gs a, atTime W gs a (p.1 + 1) p.2 = some q ∧
      ∀ s ≤ p.1, ∀ i, atTime W gs a s i ≠ some q := by
  classical
  let P : Nat → Prop := fun s => s ≤ gs.length ∧ ∃ i, atTime W gs a s i = some q
  have hex : ∃ s, P s := hv
  let t := Nat.find hex
  have ht : P t := Nat.find_spec hex
  obtain ⟨i, hti⟩ := ht.2
  have ht0 : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    exact hi i (by simpa [hz, atTime, run] using hti)
  have hmin : ∀ s < t, ∀ j, atTime W gs a s j ≠ some q := by
    intro s hs j hj
    exact Nat.find_min hex hs ⟨by omega, j, hj⟩
  have he : t - 1 + 1 = t := by omega
  refine ⟨(t - 1, i), (BirthOccurrences.occurrence_iff W gs a (t - 1) i).mpr
    ⟨by omega, ?_, ?_⟩, ?_, ?_⟩
  · simp [he, hti]
  · rw [he, hti]
    exact Ne.symm (hmin (t - 1) (by omega) i)
  · simpa only [he] using hti
  · intro s hs j
    exact hmin s (by omega) j

/-- Distinct required noninitial vectors yield distinct globally first births.
If there are no more births than required vectors, those are all the births. -/
theorem required_saturation {r : Nat} (W : Submodule F V) (gs : List (Circuit.Gate n))
    (a : Rows n V) (required : Fin r → V) (hr : Function.Injective required)
    (hi : ∀ j i, visible W a i ≠ some (required j))
    (hv : ∀ j, ∃ s ≤ gs.length, ∃ i, atTime W gs a s i = some (required j))
    (hb : CircuitLedger.totalBirths W gs a ≤ r) :
    CircuitLedger.totalBirths W gs a = r ∧ Saturation.GloballyFresh W gs a := by
  classical
  have hh := fun j => first_birth W gs a (required j) (hi j) (hv j)
  choose d hd hdv hdf using hh
  have hinj : Function.Injective d := by
    intro j k hjk
    apply hr
    have he := congrArg (fun p : Occurrence n => atTime W gs a (p.1 + 1) p.2) hjk
    rw [hdv j, hdv k] at he
    exact Option.some.inj he
  have hmap : Set.MapsTo d (Finset.univ : Finset (Fin r)) (occurrences W gs a) :=
    fun j _ => hd j
  have hl := Finset.card_le_card_of_injOn d hmap hinj.injOn
  have hsurj := Finset.surjOn_of_injOn_of_card_le d hmap hinj.injOn
    (by simpa [BirthOccurrences.occurrences_card] using hb)
  constructor
  · have hrb : r ≤ CircuitLedger.totalBirths W gs a := by
      simpa [BirthOccurrences.occurrences_card] using hl
    omega
  · intro k i q hki hvq s hs j
    obtain ⟨v, _, he⟩ := hsurj hki
    have hv' := hdv v
    have hf' := hdf v
    rw [he] at hv' hf'
    have heq : required v = q := Option.some.inj (hv'.symm.trans hvq)
    simpa only [heq] using hf' s hs j

/-- Under the same exhausted budget, every birth value belongs to the required
family. This retains the information needed by the classical path argument. -/
theorem required_birth_value {r : Nat} (W : Submodule F V) (gs : List (Circuit.Gate n))
    (a : Rows n V) (required : Fin r → V) (hr : Function.Injective required)
    (hi : ∀ j i, visible W a i ≠ some (required j))
    (hv : ∀ j, ∃ s ≤ gs.length, ∃ i, atTime W gs a s i = some (required j))
    (hb : CircuitLedger.totalBirths W gs a ≤ r)
    (p : Occurrence n) (hp : p ∈ occurrences W gs a) (q : V)
    (hq : atTime W gs a (p.1 + 1) p.2 = some q) : ∃ j, q = required j := by
  classical
  have hh := fun j => first_birth W gs a (required j) (hi j) (hv j)
  choose d hd hdv hdf using hh
  have hinj : Function.Injective d := by
    intro j k hjk
    apply hr
    have he := congrArg (fun p : Occurrence n => atTime W gs a (p.1 + 1) p.2) hjk
    rw [hdv j, hdv k] at he
    exact Option.some.inj he
  have hmap : Set.MapsTo d (Finset.univ : Finset (Fin r)) (occurrences W gs a) := fun j _ => hd j
  have hsurj := Finset.surjOn_of_injOn_of_card_le d hmap hinj.injOn
    (by simpa [BirthOccurrences.occurrences_card] using hb)
  obtain ⟨j, _, he⟩ := hsurj hp
  refine ⟨j, Option.some.inj ?_⟩
  exact hq.symm.trans (by simpa only [he] using hdv j)

/-- The birth budget alone supplies both hypotheses of the geometric
saturation theorem; neither freshness nor B=L is assumed by the caller. -/
theorem actual_required_all_T {r : Nat} (gs : List (Circuit.Gate n))
    (hlinear : ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false)
    (required : Fin r → StandardSpace.Space n) (hr : Function.Injective required)
    (hi : ∀ j i, (StandardSpace.standard n).x i ≠ required j)
    (hv : ∀ j, ∃ s ≤ gs.length, ∃ i,
      atTime (StandardSpace.initialW n) gs (StandardSpace.standard n) s i = some (required j))
    (hcost : Circuit.cost gs ≤ r) :
    Circuit.cost gs = r ∧
      CircuitLedger.totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n) = r ∧
      Saturation.GloballyFresh (StandardSpace.initialW n) gs (StandardSpace.standard n) ∧
      ∀ e ∈ CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n), e = .T := by
  have hb := (CircuitLedger.actual_linear_birth_bound gs hlinear).1
  have hs := required_saturation (StandardSpace.initialW n) gs (StandardSpace.standard n)
    required hr (fun j i => by simpa only [CircuitLedger.initial_visible, ne_eq, Option.some.injEq] using hi j i)
    hv (hb.trans hcost)
  have hcr : Circuit.cost gs = r := by omega
  refine ⟨hcr, hs.1, hs.2, ?_⟩
  exact Saturation.actual_all_T gs hlinear (hs.1.trans hcr.symm) hs.2

end CliffordSynthesis.Freshness
