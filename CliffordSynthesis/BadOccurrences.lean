/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.BirthHistory

/-!
# Bad Occurrences

Appearances outside type T gates and returns of listed pairs, as a set
of actual occurrences. Their cardinality is bounded by 3M + 4Z. `birth` denotes
an appearance on one qubit.
-/

@[expose] public section

namespace CliffordSynthesis.BadOccurrences

open LinearMap (BilinForm)
open Planes (F)
open SymplecticCircuit (Rows IsSymplectic run applyGate)
open PairInventory (event step evolve)
open BirthOccurrences (Occurrence shift stepWires occurrences)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

attribute [local instance] Classical.propDecidable

def Good (W : Submodule F V) (a : Rows n V) (m : Matching.State n) (c t : Fin n) : Prop :=
  event W a c t = .T ∨ (event W a c t = .U ∧ m.mate c = some t)

noncomputable def badWires (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (g : Circuit.Gate n) : Finset (Fin n) :=
  Circuit.Gate.casesOn g (fun _ => ∅) (fun _ => ∅)
    (fun c t hct => if Good W a m c t then ∅ else stepWires W a (applyGate (.CX c t hct) a))

theorem badWires_card (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (g : Circuit.Gate n) :
    (badWires W a m g).card = PairAccounting.bad W a m g := by
  cases g with
  | H q => rfl
  | S q => rfl
  | CX c t hct =>
    change (badWires W a m (.CX c t hct)).card = PairAccounting.paidBad W a m c t
    rw [PairAccounting.paidBad_actual B W hW a ha m c t hct]
    by_cases hg : Good W a m c t
    all_goals simp only [Good] at hg
    all_goals simp [badWires, Good, hg, BirthOccurrences.stepWires_card, applyGate]

noncomputable def badOccurrences (W : Submodule F V) (gs : List (Circuit.Gate n)) :
    Rows n V → Matching.State n → Finset (Occurrence n) :=
  gs.rec (fun _ _ => ∅) (fun g _ tail a m =>
    (badWires W a m g).image (fun i => (0, i)) ∪
      (tail (applyGate g a) (step W a m g)).image shift)

private theorem disjoint_times (s : Finset (Fin n)) (t : Finset (Occurrence n)) :
    Disjoint (s.image (fun i => (0, i))) (t.image shift) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hq
  have ht := congrArg Prod.fst hq
  simp [shift] at ht

theorem badOccurrences_card (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) :
    (badOccurrences W gs a m).card = PairAccounting.badBirths W gs a m := by
  induction gs generalizing a m with
  | nil => rfl
  | cons g gs ih =>
    change Finset.card ((badWires W a m g).image (fun i => (0, i)) ∪
      (badOccurrences W gs (applyGate g a) (step W a m g)).image shift) = _
    rw [Finset.card_union_of_disjoint (disjoint_times _ _),
      Finset.card_image_of_injective _ (fun i j h => Prod.mk.inj h |>.2),
      Finset.card_image_of_injective _ BirthOccurrences.shift_injective,
      badWires_card B W hW a ha m g,
      ih (applyGate g a) (SymplecticCircuit.gate_symplectic B a ha g) (step W a m g)]
    rfl

private theorem step_subset (W : Submodule F V) (a : Rows n V) (m : Matching.State n) (g : Circuit.Gate n) :
    badWires W a m g ⊆ stepWires W a (applyGate g a) := by
  cases g <;> simp only [badWires]
  · exact Finset.empty_subset _
  · exact Finset.empty_subset _
  · split_ifs
    · exact Finset.empty_subset _
    · exact Finset.Subset.refl _

theorem badOccurrences_subset (W : Submodule F V) (gs : List (Circuit.Gate n))
    (a : Rows n V) (m : Matching.State n) : badOccurrences W gs a m ⊆ occurrences W gs a := by
  induction gs generalizing a m with
  | nil => exact Finset.Subset.refl _
  | cons g gs ih =>
    exact Finset.union_subset_union (Finset.image_mono _ (step_subset W a m g))
      (Finset.image_mono _ (ih (applyGate g a) (step W a m g)))

private theorem mem_zero (W : Submodule F V) (g : Circuit.Gate n) (gs : List (Circuit.Gate n))
    (a : Rows n V) (m : Matching.State n) (i : Fin n) :
    (0, i) ∈ badOccurrences W (g :: gs) a m ↔ i ∈ badWires W a m g := by
  simp [badOccurrences, Finset.mem_image, shift]

private theorem mem_succ (W : Submodule F V) (g : Circuit.Gate n) (gs : List (Circuit.Gate n))
    (a : Rows n V) (m : Matching.State n) (k : Nat) (i : Fin n) :
    (k + 1, i) ∈ badOccurrences W (g :: gs) a m ↔
      (k, i) ∈ badOccurrences W gs (applyGate g a) (step W a m g) := by
  simp [badOccurrences, Finset.mem_image, shift, Prod.exists]

/-- Membership at a specified gate uses the matching constructed on its prefix. -/
theorem mem_at_prefix (W : Submodule F V) (pre : List (Circuit.Gate n))
    (g : Circuit.Gate n) (post : List (Circuit.Gate n)) (a : Rows n V)
    (m : Matching.State n) (i : Fin n) :
    (pre.length, i) ∈ badOccurrences W (pre ++ g :: post) a m ↔
      i ∈ badWires W (run pre a) (evolve W pre a m) g := by
  induction pre generalizing a m with
  | nil => exact mem_zero W g post a m i
  | cons h pre ih =>
    simpa only [List.cons_append, List.length_cons, mem_succ, run, evolve] using
      ih (applyGate h a) (step W a m h)

/-- Decompose any non-exceptional-origin birth at its actual CNOT, including
the constructed matching immediately before that gate. -/
theorem nonbad_birth (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n)
    (k : Nat) (i : Fin n) (hp : (k, i) ∈ occurrences W gs a)
    (hn : (k, i) ∉ badOccurrences W gs a m) :
    ∃ pre c t, ∃ hct : c ≠ t, ∃ post, gs = pre ++ .CX c t hct :: post ∧ k = pre.length ∧
      (i = c ∨ i = t) ∧ Good W (run pre a) (evolve W pre a m) c t := by
  induction gs generalizing a m k with
  | nil => simp [occurrences] at hp
  | cons g gs ih =>
    cases k with
    | zero =>
      have hp' : i ∈ stepWires W a (applyGate g a) := by
        simpa [BirthOccurrences.occurrences_cons, Finset.mem_image, shift] using hp
      have hn' : i ∉ badWires W a m g := by simpa only [mem_zero] using hn
      have hv := (BirthOccurrences.mem_stepWires W a (applyGate g a) i).mp hp'
      cases g with
      | H q => simp [applyGate, Observation.hadamard_visible B W hW a ha] at hv
      | S q => simp [applyGate, Observation.phase_visible B W hW a ha] at hv
      | CX c t hct =>
        have hi : i = c ∨ i = t := by
          by_contra h
          push Not at h
          simp [applyGate, Observation.cnot_untouched W a c t i h.1 h.2] at hv
        have hg : Good W a m c t := by
          by_contra hg
          exact hn' (by simpa [badWires, hg] using hp')
        exact ⟨[], c, t, hct, gs, rfl, rfl, hi, hg⟩
    | succ k =>
      have hp' : (k, i) ∈ occurrences W gs (applyGate g a) := by
        simpa [BirthOccurrences.occurrences_cons, Finset.mem_image, shift, Prod.exists] using hp
      have hn' : (k, i) ∉ badOccurrences W gs (applyGate g a) (step W a m g) := by
        simpa only [mem_succ] using hn
      obtain ⟨pre, c, t, hct, post, heq, hk, hi, hg⟩ := ih (applyGate g a)
        (SymplecticCircuit.gate_symplectic B a ha g) (step W a m g) k hp' hn'
      refine ⟨g :: pre, c, t, hct, post, ?_, ?_, hi, hg⟩
      · simp [heq]
      · simp [hk]

theorem actual_bad_card (gs : List (Circuit.Gate n)) :
    (badOccurrences (StandardSpace.initialW n) gs (StandardSpace.standard n) (Matching.empty n)).card ≤
      5 * Ledger.exceptional (CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  rw [badOccurrences_card _ _ (StandardSpace.initialW_isotropic n) _ _ (StandardSpace.standard_symplectic n)]
  exact PairAccounting.actual_bad_birth_bound gs

/-- The sharp bound on appearances outside T gates and returns of listed pairs. -/
theorem actual_bad_card_sharp (gs : List (Circuit.Gate n)) :
    (badOccurrences (StandardSpace.initialW n) gs (StandardSpace.standard n) (Matching.empty n)).card ≤
      Ledger.markCharge (CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  rw [badOccurrences_card _ _ (StandardSpace.initialW_isotropic n) _ _ (StandardSpace.standard_symplectic n)]
  exact PairAccounting.actual_bad_birth_sharp_bound gs

/-- The same bound written as 3M + 4Z. -/
theorem actual_bad_card_counts (gs : List (Circuit.Gate n)) :
    let es := CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)
    (badOccurrences (StandardSpace.initialW n) gs (StandardSpace.standard n) (Matching.empty n)).card ≤
      3 * Ledger.countM es + 4 * Ledger.countZ es := by
  simpa only [Ledger.markCharge_eq] using actual_bad_card_sharp gs

theorem actual_bad_card_linear (gs : List (Circuit.Gate n))
    (hlinear : ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false) :
    (badOccurrences (StandardSpace.initialW n) gs (StandardSpace.standard n) (Matching.empty n)).card ≤
      6 * (Circuit.cost gs - CircuitLedger.totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n)) :=
  (actual_bad_card_sharp gs).trans (PairAccounting.actual_linear_markCharge_bound gs hlinear)

end CliffordSynthesis.BadOccurrences
