/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.PairInventory

/-!
# Pair Accounting

Counting appearances outside type T gates and returns of listed pairs.
The marked set consists of the unrepresented qubits outside the matching.
A type P gate consumes one mark, a type U gate outside the matching consumes
two, and types M and Z add at most three and four, respectively. This gives
the bound 3M + 4Z ≤ 6(L-B).
-/

@[expose] public section

namespace CliffordSynthesis.PairAccounting

open LinearMap (BilinForm)
open Planes (F)
open SymplecticCircuit (Rows IsSymplectic CX applyGate)
open Observation (visible)
open PairInventory (Valid event paidStep step evolve)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

attribute [local instance] Classical.propDecidable

noncomputable def marked (W : Submodule F V) (a : Rows n V) (m : Matching.State n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => visible W a i = none ∧ m.mate i = none)

theorem mem_marked (W : Submodule F V) (a : Rows n V) (m : Matching.State n) (i : Fin n) :
    i ∈ marked W a m ↔ visible W a i = none ∧ m.mate i = none := by simp [marked]

private theorem outside_mate (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (c t i : Fin n) (hct : c ≠ t) (hi : i ∉ Matching.affected m c t) :
    (paidStep W a m c t hct).mate i = m.mate i := by
  have hi' := hi
  simp only [Matching.mem_affected, not_or] at hi'
  unfold paidStep
  split_ifs <;> simp [Matching.insert_mate, Matching.erase_mate, hi, hi'.1, hi'.2.1]

/-- All newly marked wires are among the endpoints and their old partners. -/
theorem marked_paid_subset (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (c t : Fin n) (hct : c ≠ t) :
    marked W (CX c t a) (paidStep W a m c t hct) ⊆ marked W a m ∪ Matching.affected m c t := by
  intro i hi
  by_cases hiA : i ∈ Matching.affected m c t
  · exact Finset.mem_union_right _ hiA
  · apply Finset.mem_union_left
    have hi' := hiA
    simp only [Matching.mem_affected, not_or] at hi'
    rw [mem_marked] at hi ⊢
    simpa only [outside_mate W a m c t i hct hiA,
      Observation.cnot_untouched W a c t i hi'.1 hi'.2.1] using hi

theorem marked_paid_le (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (c t : Fin n) (hct : c ≠ t) :
    (marked W (CX c t a) (paidStep W a m c t hct)).card ≤ (marked W a m).card + 4 := by
  have h₁ := Finset.card_le_card (marked_paid_subset W a m c t hct)
  have h₂ := Finset.card_union_le (marked W a m) (Matching.affected m c t)
  have h₃ := Matching.affected_card m c t
  omega

private theorem affected_of_unpaired (m : Matching.State n) (c t : Fin n)
    (hc : m.mate c = none) (ht : m.mate t = none) : Matching.affected m c t = {c, t} := by
  simp [Matching.affected, hc, ht]

private theorem affected_of_paired (m : Matching.State n) (c t : Fin n)
    (hc : m.mate c = some t) (ht : m.mate t = some c) : Matching.affected m c t = {c, t} := by
  ext i
  simp [Matching.mem_affected, hc, ht, or_comm, or_left_comm, eq_comm]

private theorem visible_not_marked (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (i : Fin n) (hi : (visible W a i).isSome = true) : i ∉ marked W a m := by
  intro hm
  simp [(mem_marked W a m i).mp hm |>.1] at hi

private theorem subset_erase (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (c t : Fin n) (hct : c ≠ t) (hA : Matching.affected m c t = {c, t})
    (hc : c ∉ marked W (CX c t a) (paidStep W a m c t hct))
    (ht : t ∉ marked W (CX c t a) (paidStep W a m c t hct)) :
    marked W (CX c t a) (paidStep W a m c t hct) ⊆ ((marked W a m).erase c).erase t := by
  intro i hi
  have hic : i ≠ c := fun hic => hc (hic ▸ hi)
  have hit : i ≠ t := fun hit => ht (hit ▸ hi)
  refine Finset.mem_erase.mpr ⟨hit, Finset.mem_erase.mpr ⟨hic, ?_⟩⟩
  have hm := marked_paid_subset W a m c t hct hi
  rcases Finset.mem_union.mp hm with hm | hm
  · exact hm
  · simp [hA, hic, hit] at hm

private theorem le_of_subset_erase (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (c t : Fin n) (hct : c ≠ t)
    (hs : marked W (CX c t a) (paidStep W a m c t hct) ⊆ ((marked W a m).erase c).erase t) :
    (marked W (CX c t a) (paidStep W a m c t hct)).card ≤ (marked W a m).card :=
  Finset.card_le_card (hs.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))

theorem T_marked_le (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) (he : event W a c t = .T) :
    (marked W (CX c t a) (paidStep W a m c t hct)).card ≤ (marked W a m).card := by
  have hb := PairInventory.before_two B W hW a ha c t hct (by rw [he]; rfl)
  have hf := PairInventory.after_two B W hW a ha c t hct (by rw [he]; rfl)
  have hc := PairInventory.visible_unpaired B W a m hm c hb.1
  have ht := PairInventory.visible_unpaired B W a m hm t hb.2
  exact le_of_subset_erase W a m c t hct (subset_erase W a m c t hct
    (affected_of_unpaired m c t hc ht) (visible_not_marked W _ _ c hf.1) (visible_not_marked W _ _ t hf.2))

theorem D_marked_le (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) (he : event W a c t = .D) :
    (marked W (CX c t a) (paidStep W a m c t hct)).card ≤ (marked W a m).card := by
  have hb := PairInventory.before_two B W hW a ha c t hct (by rw [he]; rfl)
  have hc := PairInventory.visible_unpaired B W a m hm c hb.1
  have ht := PairInventory.visible_unpaired B W a m hm t hb.2
  apply le_of_subset_erase W a m c t hct
  apply subset_erase W a m c t hct (affected_of_unpaired m c t hc ht)
  · simp [mem_marked, paidStep, he, Matching.insert_mate]
  · simp [mem_marked, paidStep, he, Matching.insert_mate, Ne.symm hct]

theorem U_clean_marked_le (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n)
    (c t : Fin n) (hct : c ≠ t) (he : event W a c t = .U) (hc : m.mate c = some t) :
    (marked W (CX c t a) (paidStep W a m c t hct)).card ≤ (marked W a m).card := by
  have hf := PairInventory.after_two B W hW a ha c t hct (by rw [he]; rfl)
  exact le_of_subset_erase W a m c t hct (subset_erase W a m c t hct
    (affected_of_paired m c t hc (m.symmetric c t hc))
    (visible_not_marked W _ _ c hf.1) (visible_not_marked W _ _ t hf.2))

/-- A non-clean U consumes two distinct previously marked hidden wires. -/
theorem U_marked_consumes_two (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) (he : event W a c t = .U) (hc : m.mate c ≠ some t) :
    2 + (marked W (CX c t a) (paidStep W a m c t hct)).card ≤ (marked W a m).card := by
  have hd := PairInventory.U_dichotomy B W hW a ha m hm c t hct he
  rcases hd with hd | ⟨hmc, hmt⟩
  · exact False.elim (hc hd.1)
  · have hb := PairInventory.before_zero B W hW a ha c t hct (by rw [he]; rfl)
    have hf := PairInventory.after_two B W hW a ha c t hct (by rw [he]; rfl)
    have hsub := subset_erase W a m c t hct (affected_of_unpaired m c t hmc hmt)
      (visible_not_marked W _ _ c hf.1) (visible_not_marked W _ _ t hf.2)
    have hcard := Finset.card_le_card hsub
    have hcm : c ∈ marked W a m := (mem_marked W a m c).mpr ⟨hb.1, hmc⟩
    have htm : t ∈ (marked W a m).erase c := by
      simp [Finset.mem_erase, Ne.symm hct, mem_marked, hb.2, hmt]
    have h₁ := Finset.card_erase_add_one hcm
    have h₂ := Finset.card_erase_add_one htm
    omega

/-- A type P gate removes one of its two marked hidden participants. -/
theorem P_marked_consumes_one (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) (he : event W a c t = .P) :
    1 + (marked W (CX c t a) (paidStep W a m c t hct)).card ≤ (marked W a m).card := by
  have hb := PairInventory.before_zero B W hW a ha c t hct (by rw [he]; rfl)
  have hu := PairInventory.P_unpaired B W hW a ha m hm c t hct he
  have hc : c ∈ marked W a m := (mem_marked W a m c).mpr ⟨hb.1, hu.1⟩
  have ht : t ∈ marked W a m := (mem_marked W a m t).mpr ⟨hb.2, hu.2⟩
  have hA : Matching.affected m c t ⊆ marked W a m := by
    rw [affected_of_unpaired m c t hu.1 hu.2]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hc
    · exact (Finset.mem_singleton.mp hi) ▸ ht
  have hsub : marked W (CX c t a) (paidStep W a m c t hct) ⊆ marked W a m :=
    (marked_paid_subset W a m c t hct).trans (Finset.union_subset (Finset.Subset.refl _) hA)
  have drop (q : Fin n) (hq : q ∈ marked W a m)
      (hv : (visible W (CX c t a) q).isSome = true) :
      1 + (marked W (CX c t a) (paidStep W a m c t hct)).card ≤ (marked W a m).card := by
    have hqn := visible_not_marked W (CX c t a) (paidStep W a m c t hct) q hv
    have hse : marked W (CX c t a) (paidStep W a m c t hct) ⊆ (marked W a m).erase q := by
      intro i hi
      exact Finset.mem_erase.mpr ⟨(fun h => hqn (h ▸ hi)), hsub hi⟩
    have hcard := Finset.card_le_card hse
    have herase := Finset.card_erase_add_one hq
    omega
  have hs := CircuitLedger.classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
  have hf : Observation.present (visible W (CX c t a) c) +
      Observation.present (visible W (CX c t a) t) = 1 :=
    hs.2.1.symm.trans (by change (event W a c t).after = 1; rw [he]; rfl)
  have hv : (visible W (CX c t a) c).isSome = true ∨
      (visible W (CX c t a) t).isSome = true := by
    cases hvc : visible W (CX c t a) c <;> cases hvt : visible W (CX c t a) t <;>
      simp_all [Observation.present]
  exact hv.elim (drop c hc) (drop t ht)

private theorem affected_card_of_unpaired (m : Matching.State n) (c t : Fin n)
    (hu : m.mate c = none ∨ m.mate t = none) : (Matching.affected m c t).card ≤ 3 := by
  have hc : (m.mate c).toFinset.card ≤ 1 := by cases m.mate c <;> simp
  have ht : (m.mate t).toFinset.card ≤ 1 := by cases m.mate t <;> simp
  have h₁ := Finset.card_union_le ({c, t} ∪ (m.mate c).toFinset) (m.mate t).toFinset
  have h₂ := Finset.card_union_le {c, t} (m.mate c).toFinset
  have h₃ : ({c, t} : Finset (Fin n)).card ≤ 2 := by
    by_cases hct : c = t <;> simp [hct]
  dsimp only [Matching.affected]
  rcases hu with hu | hu <;> simp only [hu, Option.toFinset_none, Finset.card_empty] at * <;> omega

/-- At a type M gate one participant is visible, so at most one listed pair
can be broken and at most three hidden wires become marked. -/
theorem M_marked_le (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) (he : event W a c t = .M) :
    (marked W (CX c t a) (paidStep W a m c t hct)).card ≤ (marked W a m).card + 3 := by
  have hs := CircuitLedger.classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
  have hb : Observation.present (visible W a c) + Observation.present (visible W a t) = 1 :=
    hs.1.symm.trans (by change (event W a c t).before = 1; rw [he]; rfl)
  have hv : (visible W a c).isSome = true ∨ (visible W a t).isSome = true := by
    cases hvc : visible W a c <;> cases hvt : visible W a t <;> simp_all [Observation.present]
  have hu : m.mate c = none ∨ m.mate t = none :=
    hv.imp (PairInventory.visible_unpaired B W a m hm c) (PairInventory.visible_unpaired B W a m hm t)
  have h₁ := Finset.card_le_card (marked_paid_subset W a m c t hct)
  have h₂ := Finset.card_union_le (marked W a m) (Matching.affected m c t)
  have h₃ := affected_card_of_unpaired m c t hu
  omega

/-- Births other than a type-T update or an intact untouched-pair return. -/
noncomputable def paidBad (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (c t : Fin n) : Nat :=
  if event W a c t = .T ∨ (event W a c t = .U ∧ m.mate c = some t) then 0
  else (event W a c t).births

theorem paidBad_actual (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n)
    (c t : Fin n) (hct : c ≠ t) :
    paidBad W a m c t =
      if event W a c t = .T ∨ (event W a c t = .U ∧ m.mate c = some t) then 0
      else Observation.stepBirths W a (CX c t a) := by
  have hs := CircuitLedger.classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
  unfold paidBad
  rw [Observation.cnot_births W a c t hct]
  exact congrArg (fun k => if event W a c t = .T ∨
    (event W a c t = .U ∧ m.mate c = some t) then 0 else k) hs.2.2

/-- Local potential inequality. Only exceptional gates can replenish the
marked-wire potential, by at most four, and each has at most one birth. -/
theorem paid_potential (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) :
    paidBad W a m c t + (marked W (CX c t a) (paidStep W a m c t hct)).card ≤
      (marked W a m).card + 5 * (event W a c t).exceptional := by
  cases he : event W a c t with
  | T => simpa [paidBad, he, Ledger.Event.exceptional] using T_marked_le B W hW a ha m hm c t hct he
  | D => simpa [paidBad, he, Ledger.Event.exceptional, Ledger.Event.births] using
      D_marked_le B W hW a ha m hm c t hct he
  | U =>
    by_cases hc : m.mate c = some t
    · simpa [paidBad, he, hc, Ledger.Event.exceptional] using
        U_clean_marked_le B W hW a ha m c t hct he hc
    · simpa [paidBad, he, hc, Ledger.Event.exceptional, Ledger.Event.births] using
        U_marked_consumes_two B W hW a ha m hm c t hct he hc
  | P | M | Z₂ | Z₁ | Z₀ =>
    have hh := marked_paid_le W a m c t hct
    simp only [paidBad, he, Ledger.Event.exceptional, Ledger.Event.births] at *
    simp at *
    omega

noncomputable def bad (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (g : Circuit.Gate n) : Nat :=
  Circuit.Gate.casesOn g (fun _ => 0) (fun _ => 0) (fun c t _ => paidBad W a m c t)

noncomputable def exceptions (W : Submodule F V) (a : Rows n V) (g : Circuit.Gate n) : Nat :=
  Circuit.Gate.casesOn g (fun _ => 0) (fun _ => 0) (fun c t _ => (event W a c t).exceptional)

theorem gate_potential (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (g : Circuit.Gate n) :
    bad W a m g + (marked W (applyGate g a) (step W a m g)).card ≤
      (marked W a m).card + 5 * exceptions W a g := by
  cases g with
  | H q => simp [bad, step, applyGate, exceptions, marked, Observation.hadamard_visible B W hW a ha]
  | S q => simp [bad, step, applyGate, exceptions, marked, Observation.phase_visible B W hW a ha]
  | CX c t hct => exact paid_potential B W hW a ha m hm c t hct

noncomputable def badBirths (W : Submodule F V) (gs : List (Circuit.Gate n)) :
    Rows n V → Matching.State n → Nat :=
  gs.rec (fun _ _ => 0) (fun g _ tail a m => bad W a m g + tail (applyGate g a) (step W a m g))

theorem history_potential (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (m : Matching.State n) (hm : Valid B W a m) :
    badBirths W gs a m + (marked W (SymplecticCircuit.run gs a) (evolve W gs a m)).card ≤
      (marked W a m).card + 5 * Ledger.exceptional (CircuitLedger.trace W gs a) := by
  induction gs generalizing a m with
  | nil => simp [badBirths, SymplecticCircuit.run, evolve, CircuitLedger.trace, Ledger.exceptional]
  | cons g gs ih =>
    have hi := ih (applyGate g a) (SymplecticCircuit.gate_symplectic B a ha g)
      (step W a m g) (PairInventory.step_valid B W hW a ha m hm g)
    have hp := gate_potential B W hW a ha m hm g
    have he : Ledger.exceptional (CircuitLedger.trace W (g :: gs) a) =
        exceptions W a g + Ledger.exceptional (CircuitLedger.trace W gs (applyGate g a)) := by
      cases g <;> simp [CircuitLedger.trace, Ledger.exceptional, exceptions, event, applyGate]
    change bad W a m g + badBirths W gs (applyGate g a) (step W a m g) +
        (marked W (SymplecticCircuit.run gs (applyGate g a))
          (evolve W gs (applyGate g a) (step W a m g))).card ≤ _
    rw [he]
    omega

/-- A coarse 5h estimate for the constructed inventory.
`actual_bad_birth_sharp_bound` separates the M and Z contributions. -/
theorem actual_bad_birth_bound (gs : List (Circuit.Gate n)) :
    badBirths (StandardSpace.initialW n) gs (StandardSpace.standard n) (Matching.empty n) ≤
      5 * Ledger.exceptional
        (CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  have hh := history_potential (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) gs _ (StandardSpace.standard_symplectic n)
    (Matching.empty n) (PairInventory.empty_valid _ _ _)
  have hz : marked (StandardSpace.initialW n) (StandardSpace.standard n) (Matching.empty n) = ∅ := by
    ext i
    simp [mem_marked, CircuitLedger.initial_visible]
  rw [hz, Finset.card_empty, zero_add] at hh
  omega

/-- The sharp local charge: P removes one mark, M adds at most three,
and each Z adds at most four. Clean T and U gates have no charge. -/
theorem paid_sharp_potential (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) :
    paidBad W a m c t + (marked W (CX c t a) (paidStep W a m c t hct)).card ≤
      (marked W a m).card + (event W a c t).markCharge := by
  cases he : event W a c t with
  | T => simpa [paidBad, he, Ledger.Event.markCharge] using T_marked_le B W hW a ha m hm c t hct he
  | D => simpa [paidBad, he, Ledger.Event.markCharge, Ledger.Event.births] using
      D_marked_le B W hW a ha m hm c t hct he
  | U =>
    by_cases hc : m.mate c = some t
    · simpa [paidBad, he, hc, Ledger.Event.markCharge] using
        U_clean_marked_le B W hW a ha m c t hct he hc
    · simpa [paidBad, he, hc, Ledger.Event.markCharge, Ledger.Event.births] using
        U_marked_consumes_two B W hW a ha m hm c t hct he hc
  | P => simpa [paidBad, he, Ledger.Event.markCharge, Ledger.Event.births] using
      P_marked_consumes_one B W hW a ha m hm c t hct he
  | M => simpa [paidBad, he, Ledger.Event.markCharge, Ledger.Event.births] using
      M_marked_le B W hW a ha m hm c t hct he
  | Z₂ | Z₁ | Z₀ =>
    simpa [paidBad, he, Ledger.Event.markCharge, Ledger.Event.births] using marked_paid_le W a m c t hct

noncomputable def markChargeStep (W : Submodule F V) (a : Rows n V) (g : Circuit.Gate n) : Nat :=
  Circuit.Gate.casesOn g (fun _ => 0) (fun _ => 0) (fun c t _ => (event W a c t).markCharge)

theorem gate_sharp_potential (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (g : Circuit.Gate n) :
    bad W a m g + (marked W (applyGate g a) (step W a m g)).card ≤
      (marked W a m).card + markChargeStep W a g := by
  cases g with
  | H q => simp [bad, step, applyGate, markChargeStep, marked, Observation.hadamard_visible B W hW a ha]
  | S q => simp [bad, step, applyGate, markChargeStep, marked, Observation.phase_visible B W hW a ha]
  | CX c t hct => exact paid_sharp_potential B W hW a ha m hm c t hct

/-- Telescope the marked-set potential along the actual circuit. -/
theorem history_sharp_potential (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (m : Matching.State n) (hm : Valid B W a m) :
    badBirths W gs a m + (marked W (SymplecticCircuit.run gs a) (evolve W gs a m)).card ≤
      (marked W a m).card + Ledger.markCharge (CircuitLedger.trace W gs a) := by
  induction gs generalizing a m with
  | nil => simp [badBirths, SymplecticCircuit.run, evolve, CircuitLedger.trace, Ledger.markCharge]
  | cons g gs ih =>
    have hi := ih (applyGate g a) (SymplecticCircuit.gate_symplectic B a ha g)
      (step W a m g) (PairInventory.step_valid B W hW a ha m hm g)
    have hp := gate_sharp_potential B W hW a ha m hm g
    have he : Ledger.markCharge (CircuitLedger.trace W (g :: gs) a) =
        markChargeStep W a g + Ledger.markCharge (CircuitLedger.trace W gs (applyGate g a)) := by
      cases g <;> simp [CircuitLedger.trace, Ledger.markCharge, markChargeStep, event, applyGate]
    change bad W a m g + badBirths W gs (applyGate g a) (step W a m g) +
        (marked W (SymplecticCircuit.run gs (applyGate g a))
          (evolve W gs (applyGate g a) (step W a m g))).card ≤ _
    rw [he]
    omega

/-- Appearances outside T gates and returns of listed pairs number at most
3M + 4Z. The actual identity begins with no hidden or marked qubits. -/
theorem actual_bad_birth_sharp_bound (gs : List (Circuit.Gate n)) :
    badBirths (StandardSpace.initialW n) gs (StandardSpace.standard n) (Matching.empty n) ≤
      Ledger.markCharge (CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  have hh := history_sharp_potential (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) gs _ (StandardSpace.standard_symplectic n)
    (Matching.empty n) (PairInventory.empty_valid _ _ _)
  have hz : marked (StandardSpace.initialW n) (StandardSpace.standard n) (Matching.empty n) = ∅ := by
    ext i
    simp [mem_marked, CircuitLedger.initial_visible]
  rw [hz, Finset.card_empty, zero_add] at hh
  omega

theorem actual_bad_birth_count_bound (gs : List (Circuit.Gate n)) :
    let es := CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)
    badBirths (StandardSpace.initialW n) gs (StandardSpace.standard n) (Matching.empty n) ≤
      3 * Ledger.countM es + 4 * Ledger.countZ es := by
  simpa only [Ledger.markCharge_eq] using actual_bad_birth_sharp_bound gs

/-- When all output qubits represent a vector, 3M + 4Z is at most 6(L-B). -/
theorem actual_markCharge_bound (gs : List (Circuit.Gate n))
    (hfinal : Observation.count (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) = n) :
    Ledger.markCharge (CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) ≤
      6 * (Circuit.cost gs - CircuitLedger.totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  have hb := (CircuitLedger.actual_amortized gs hfinal).2.1
  have he := CircuitLedger.trace_births (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) gs _ (StandardSpace.standard_symplectic n)
  have hc := Ledger.markCharge_le_penalty
    (CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n))
  rw [he] at hb
  omega

theorem actual_linear_markCharge_bound (gs : List (Circuit.Gate n))
    (hlinear : ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false) :
    Ledger.markCharge (CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) ≤
      6 * (Circuit.cost gs - CircuitLedger.totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  apply actual_markCharge_bound gs
  apply Observation.count_of_all_x (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _ (StandardSpace.actual_run_symplectic gs)
  intro i
  simp [StandardSpace.initialW_mem, StandardSpace.fieldRows, hlinear, LocalChart.bit]

/-- Combining pair accounting with the actual birth ledger gives a bound in
terms of paid cost minus births for every linear-output circuit. -/
theorem actual_linear_bad_bound (gs : List (Circuit.Gate n))
    (hlinear : ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false) :
    badBirths (StandardSpace.initialW n) gs (StandardSpace.standard n) (Matching.empty n) ≤
      6 * (Circuit.cost gs - CircuitLedger.totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n)) :=
  (actual_bad_birth_sharp_bound gs).trans (actual_linear_markCharge_bound gs hlinear)

noncomputable def paidMarkedReturns (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (c t : Fin n) : Nat := if event W a c t = .U ∧ m.mate c ≠ some t then 2 else 0

/-- A coarse auxiliary potential bound counting only appearances at returns
of marked qubits. The full sharp bound is `paid_sharp_potential`. -/
theorem marked_return_potential (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (m : Matching.State n) (hm : Valid B W a m)
    (c t : Fin n) (hct : c ≠ t) :
    paidMarkedReturns W a m c t + (marked W (CX c t a) (paidStep W a m c t hct)).card ≤
      (marked W a m).card + 4 * (event W a c t).exceptional := by
  cases he : event W a c t with
  | T => simpa [paidMarkedReturns, he, Ledger.Event.exceptional] using T_marked_le B W hW a ha m hm c t hct he
  | D => simpa [paidMarkedReturns, he, Ledger.Event.exceptional] using D_marked_le B W hW a ha m hm c t hct he
  | U =>
    by_cases hc : m.mate c = some t
    · simpa [paidMarkedReturns, he, hc, Ledger.Event.exceptional] using
        U_clean_marked_le B W hW a ha m c t hct he hc
    · simpa [paidMarkedReturns, he, hc, Ledger.Event.exceptional] using
        U_marked_consumes_two B W hW a ha m hm c t hct he hc
  | P | M | Z₂ | Z₁ | Z₀ =>
    simpa [paidMarkedReturns, he, Ledger.Event.exceptional] using marked_paid_le W a m c t hct

noncomputable def markedReturnStep (W : Submodule F V) (a : Rows n V) (m : Matching.State n)
    (g : Circuit.Gate n) : Nat :=
  Circuit.Gate.casesOn g (fun _ => 0) (fun _ => 0) (fun c t _ => paidMarkedReturns W a m c t)

noncomputable def markedReturnBirths (W : Submodule F V) (gs : List (Circuit.Gate n)) :
    Rows n V → Matching.State n → Nat :=
  gs.rec (fun _ _ => 0) (fun g _ tail a m =>
    markedReturnStep W a m g + tail (applyGate g a) (step W a m g))

theorem marked_return_history (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (m : Matching.State n) (hm : Valid B W a m) :
    markedReturnBirths W gs a m + (marked W (SymplecticCircuit.run gs a) (evolve W gs a m)).card ≤
      (marked W a m).card + 4 * Ledger.exceptional (CircuitLedger.trace W gs a) := by
  induction gs generalizing a m with
  | nil => simp [markedReturnBirths, SymplecticCircuit.run, evolve, CircuitLedger.trace, Ledger.exceptional]
  | cons g gs ih =>
    have hi := ih (applyGate g a) (SymplecticCircuit.gate_symplectic B a ha g)
      (step W a m g) (PairInventory.step_valid B W hW a ha m hm g)
    have hp : markedReturnStep W a m g + (marked W (applyGate g a) (step W a m g)).card ≤
        (marked W a m).card + 4 * exceptions W a g := by
      cases g with
      | H q => simp [markedReturnStep, step, applyGate, exceptions, marked, Observation.hadamard_visible B W hW a ha]
      | S q => simp [markedReturnStep, step, applyGate, exceptions, marked, Observation.phase_visible B W hW a ha]
      | CX c t hct => exact marked_return_potential B W hW a ha m hm c t hct
    have he : Ledger.exceptional (CircuitLedger.trace W (g :: gs) a) =
        exceptions W a g + Ledger.exceptional (CircuitLedger.trace W gs (applyGate g a)) := by
      cases g <;> simp [CircuitLedger.trace, Ledger.exceptional, exceptions, event, applyGate]
    change markedReturnStep W a m g + markedReturnBirths W gs (applyGate g a) (step W a m g) +
        (marked W (SymplecticCircuit.run gs (applyGate g a))
          (evolve W gs (applyGate g a) (step W a m g))).card ≤ _
    rw [he]
    omega

/-- A coarse auxiliary 4h estimate on appearances at returns of marked
qubits, retained for proofs that only need the absence of exceptional gates. -/
theorem actual_marked_return_bound (gs : List (Circuit.Gate n)) :
    markedReturnBirths (StandardSpace.initialW n) gs (StandardSpace.standard n) (Matching.empty n) ≤
      4 * Ledger.exceptional
        (CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  have hh := marked_return_history (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) gs _ (StandardSpace.standard_symplectic n)
    (Matching.empty n) (PairInventory.empty_valid _ _ _)
  have hz : marked (StandardSpace.initialW n) (StandardSpace.standard n) (Matching.empty n) = ∅ := by
    ext i
    simp [mem_marked, CircuitLedger.initial_visible]
  rw [hz, Finset.card_empty, zero_add] at hh
  omega

end CliffordSynthesis.PairAccounting
