/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.PairAccounting

/-!
# Birth Occurrences

Births as distinct time-and-wire occurrences. This connects finite-set
injections used by the recorder argument to the circuit's numerical ledger.
-/

@[expose] public section

namespace CliffordSynthesis.BirthOccurrences

open Planes (F)
open SymplecticCircuit (Rows applyGate run)
open Observation (visible birth)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

attribute [local instance] Classical.propDecidable

abbrev Occurrence (n : Nat) := Nat × Fin n

def shift (p : Occurrence n) : Occurrence n := (p.1 + 1, p.2)

theorem shift_injective : Function.Injective (shift (n := n)) := by
  intro p q he
  obtain ⟨hp, hq⟩ := Prod.mk.inj he
  exact Prod.ext (by simpa using hp) hq

noncomputable def stepWires (W : Submodule F V) (a b : Rows n V) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (visible W b i).isSome = true ∧ visible W b i ≠ visible W a i)

theorem mem_stepWires (W : Submodule F V) (a b : Rows n V) (i : Fin n) :
    i ∈ stepWires W a b ↔ (visible W b i).isSome = true ∧ visible W b i ≠ visible W a i := by
  simp [stepWires]

theorem stepWires_card (W : Submodule F V) (a b : Rows n V) :
    (stepWires W a b).card = Observation.stepBirths W a b := by
  simp only [stepWires, Finset.card_filter, Observation.stepBirths, birth]

noncomputable def occurrences (W : Submodule F V) (gs : List (Circuit.Gate n)) :
    Rows n V → Finset (Occurrence n) :=
  gs.rec (fun _ => ∅) (fun g _ tail a =>
    (stepWires W a (applyGate g a)).image (fun i => (0, i)) ∪ (tail (applyGate g a)).image shift)

theorem occurrences_cons (W : Submodule F V) (g : Circuit.Gate n) (gs : List (Circuit.Gate n))
    (a : Rows n V) :
    occurrences W (g :: gs) a =
      (stepWires W a (applyGate g a)).image (fun i => (0, i)) ∪
      (occurrences W gs (applyGate g a)).image shift := rfl

private theorem disjoint_times (s : Finset (Fin n)) (t : Finset (Occurrence n)) :
    Disjoint (s.image (fun i => (0, i))) (t.image shift) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hq
  have ht := congrArg Prod.fst hq
  simp [shift] at ht

/-- The ledger counts actual distinct occurrences, including two births at
the same gate on different wires. -/
theorem occurrences_card (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V) :
    (occurrences W gs a).card = CircuitLedger.totalBirths W gs a := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [occurrences_cons, Finset.card_union_of_disjoint (disjoint_times _ _),
      Finset.card_image_of_injective _ (fun i j h => Prod.mk.inj h |>.2),
      Finset.card_image_of_injective _ shift_injective, stepWires_card, ih]
    rfl

theorem occurrence_time_lt (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (p : Occurrence n) (hp : p ∈ occurrences W gs a) : p.1 < gs.length := by
  induction gs generalizing a p with
  | nil => simp [occurrences] at hp
  | cons g gs ih =>
    rw [occurrences_cons] at hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      simp
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      simpa [shift] using Nat.add_lt_add_right (ih _ q hq) 1

/-- A noninitial visible output on a physical wire requires a birth on that
wire. No assumption about recorder/data separation is used. -/
theorem output_has_birth (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (i : Fin n) (v : V) (hout : visible W (run gs a) i = some v)
    (hin : visible W a i ≠ some v) : ∃ k, (k, i) ∈ occurrences W gs a := by
  induction gs generalizing a with
  | nil => exact False.elim (hin hout)
  | cons g gs ih =>
    by_cases hb : visible W (applyGate g a) i = some v
    · refine ⟨0, ?_⟩
      rw [occurrences_cons]
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, rfl⟩
      rw [mem_stepWires, hb]
      exact ⟨rfl, Ne.symm hin⟩
    · obtain ⟨k, hk⟩ := ih (applyGate g a) hout hb
      refine ⟨k + 1, ?_⟩
      rw [occurrences_cons]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(k, i), hk, rfl⟩)

/-- Choose one distinct birth occurrence for each distinct physical recorder
wire whose final visible vector differs from its initial vector. -/
theorem recorder_birth_injection {r : Nat} (W : Submodule F V) (gs : List (Circuit.Gate n))
    (a : Rows n V) (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (output : Fin r → V) (hout : ∀ j, visible W (run gs a) (recorder j) = some (output j))
    (hin : ∀ j, visible W a (recorder j) ≠ some (output j)) :
    ∃ designate : Fin r → Occurrence n,
      Function.Injective designate ∧ (∀ j, designate j ∈ occurrences W gs a) ∧
      (∀ j, (designate j).2 = recorder j) := by
  classical
  have hh := fun j => output_has_birth W gs a (recorder j) (output j) (hout j) (hin j)
  choose time htime using hh
  refine ⟨fun j => (time j, recorder j), ?_, htime, fun _ => rfl⟩
  intro i j hij
  exact hr (congrArg Prod.snd hij)

/-- The R ≤ B inequality used to define the excess E = B - R. -/
theorem recorder_count_le_births {r : Nat} (W : Submodule F V) (gs : List (Circuit.Gate n))
    (a : Rows n V) (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (output : Fin r → V) (hout : ∀ j, visible W (run gs a) (recorder j) = some (output j))
    (hin : ∀ j, visible W a (recorder j) ≠ some (output j)) :
    r ≤ CircuitLedger.totalBirths W gs a := by
  classical
  obtain ⟨d, hd, hmem, _⟩ := recorder_birth_injection W gs a recorder hr output hout hin
  let f : Fin r → ↥(occurrences W gs a) := fun j => ⟨d j, hmem j⟩
  have hf : Function.Injective f := fun i j hij => hd (congrArg Subtype.val hij)
  have hh := Fintype.card_le_of_injective f hf
  simpa [occurrences_card] using hh

noncomputable def atTime (W : Submodule F V) (gs : List (Circuit.Gate n))
    (a : Rows n V) (k : Nat) (i : Fin n) : Option V := visible W (run (gs.take k) a) i

private theorem mem_zero_cons (W : Submodule F V) (g : Circuit.Gate n) (gs : List (Circuit.Gate n))
    (a : Rows n V) (i : Fin n) :
    (0, i) ∈ occurrences W (g :: gs) a ↔ i ∈ stepWires W a (applyGate g a) := by
  simp [occurrences_cons, Finset.mem_image, shift]

private theorem mem_succ_cons (W : Submodule F V) (g : Circuit.Gate n) (gs : List (Circuit.Gate n))
    (a : Rows n V) (k : Nat) (i : Fin n) :
    (k + 1, i) ∈ occurrences W (g :: gs) a ↔ (k, i) ∈ occurrences W gs (applyGate g a) := by
  simp [occurrences_cons, Finset.mem_image, shift, Prod.exists]

/-- Membership has its intended semantics at the indicated circuit boundary. -/
theorem occurrence_iff (W : Submodule F V) (gs : List (Circuit.Gate n))
    (a : Rows n V) (k : Nat) (i : Fin n) :
    (k, i) ∈ occurrences W gs a ↔ k < gs.length ∧
      (atTime W gs a (k + 1) i).isSome = true ∧ atTime W gs a (k + 1) i ≠ atTime W gs a k i := by
  induction gs generalizing a k with
  | nil => simp [occurrences]
  | cons g gs ih =>
    cases k with
    | zero => simp [mem_zero_cons, mem_stepWires, atTime, run]
    | succ k =>
      rw [mem_succ_cons, ih]
      simp [atTime, List.take_succ_cons, run, Nat.add_assoc]

private theorem last_segment {α : Type*} (h : Nat → Option α) (N : Nat) (v : α)
    (hN : h N = some v) (h₀ : h 0 ≠ some v) :
    ∃ k, k < N ∧ h k ≠ some v ∧ h (k + 1) = some v ∧
      ∀ t, k + 1 ≤ t → t ≤ N → h t = some v := by
  classical
  let P : Nat → Prop := fun s => s ≤ N ∧ ∀ t, s ≤ t → t ≤ N → h t = some v
  have hex : ∃ s, P s := ⟨N, le_rfl, fun t h₁ h₂ => (show t = N by omega) ▸ hN⟩
  let s := Nat.find hex
  have hs : P s := Nat.find_spec hex
  have hs0 : 0 < s := by
    by_contra hn
    have hz : s = 0 := by omega
    exact h₀ (hs.2 0 (by omega) (by omega))
  have hk : h (s - 1) ≠ some v := by
    intro hk
    have hP : P (s - 1) := by
      refine ⟨by omega, ?_⟩
      intro t ht htn
      by_cases hts : s ≤ t
      · exact hs.2 t hts htn
      · have he : t = s - 1 := by omega
        simpa [he] using hk
    exact Nat.find_min hex (show s - 1 < s by omega) hP
  refine ⟨s - 1, by omega, hk, ?_, ?_⟩
  · apply hs.2 <;> omega
  · intro t ht htn
    exact hs.2 t (by omega) htn

/-- The birth beginning the final uninterrupted appearance exists on every
wire with a noninitial final visible vector. -/
theorem final_appearance (W : Submodule F V) (gs : List (Circuit.Gate n))
    (a : Rows n V) (i : Fin n) (v : V) (hout : visible W (run gs a) i = some v)
    (hin : visible W a i ≠ some v) :
    ∃ k, (k, i) ∈ occurrences W gs a ∧ atTime W gs a (k + 1) i = some v ∧
      (∀ t, k + 1 ≤ t → t ≤ gs.length → atTime W gs a t i = some v) := by
  have hN : atTime W gs a gs.length i = some v := by simpa [atTime] using hout
  have h₀ : atTime W gs a 0 i ≠ some v := by simpa [atTime, run] using hin
  obtain ⟨k, hk, hprev, hnew, hrest⟩ := last_segment (fun t => atTime W gs a t i) gs.length v hN h₀
  refine ⟨k, (occurrence_iff W gs a k i).mpr ⟨hk, ?_, ?_⟩, hnew, hrest⟩
  · simp [hnew]
  · rw [hnew]
    exact Ne.symm hprev

/-- Designated appearances: distinct occurrences, on their own
physical recorder wires, beginning their final uninterrupted output values. -/
theorem designated_births {r : Nat} (W : Submodule F V) (gs : List (Circuit.Gate n))
    (a : Rows n V) (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (output : Fin r → V) (hout : ∀ j, visible W (run gs a) (recorder j) = some (output j))
    (hin : ∀ j, visible W a (recorder j) ≠ some (output j)) :
    ∃ time : Fin r → Nat,
      Function.Injective (fun j => (time j, recorder j)) ∧
      (∀ j, (time j, recorder j) ∈ occurrences W gs a) ∧
      (∀ j, atTime W gs a (time j + 1) (recorder j) = some (output j)) ∧
      (∀ j t, time j + 1 ≤ t → t ≤ gs.length → atTime W gs a t (recorder j) = some (output j)) := by
  classical
  have hh := fun j => final_appearance W gs a (recorder j) (output j) (hout j) (hin j)
  choose time htime hnew hrest using hh
  refine ⟨time, ?_, htime, hnew, hrest⟩
  intro i j hij
  exact hr (congrArg Prod.snd hij)

end CliffordSynthesis.BirthOccurrences
