/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.DisplacedAlgebra
public import CliffordSynthesis.MissingParity
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Displaced Recorders

The bound for recorder outputs on arbitrary qubits. Recorder outputs may be on
arbitrary distinct final wires; no fixed-output-wire hypothesis is used.
-/

public section

namespace CliffordSynthesis.DisplacedRecorders

open LinearMap (BilinForm)
open Planes (F)
open SymplecticCircuit (Rows IsSymplectic CX run applyGate)
open Observation (visible)
open PairInventory (event evolve)
open BirthOccurrences (Occurrence occurrences atTime)
open StandardSpace (Space standard)
open RecorderVectors (parity recorder output)
open Target (Wire)
open DisplacedAlgebra

variable {V : Type*} [AddCommGroup V] [Module F V] {n d r : Nat}

/-- A nonexceptional first birth has a historical source: its difference from
the wire's initial value, or its own output on the partner wire. -/
theorem classify_source (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (i : Fin n) (k : Nat) (y f q : V) (hy : visible W a i = some y) (hq : q = y + f)
    (hinit : ∀ j, visible W a j ≠ some q) (hfinit : ∀ j, visible W a j ≠ some f)
    (hb : (k, i) ∈ occurrences W gs a) (hnew : atTime W gs a (k + 1) i = some q)
    (hearlier : ∀ l < k, (l, i) ∉ occurrences W gs a)
    (hbad : (k, i) ∉ BadOccurrences.badOccurrences W gs a (Matching.empty n)) :
    ∃ p ∈ occurrences W gs a,
      atTime W gs a (p.1 + 1) p.2 = some f ∨
      atTime W gs a (p.1 + 1) p.2 = some q ∧ p.2 ≠ i := by
  have hq_y : q ≠ y := fun h => hinit i (by simpa only [h] using hy)
  have initial_on_prefix (ps : List (Circuit.Gate n)) (hps : ps.IsPrefix gs)
      (hpk : ps.length ≤ k) (v : V) (hv : visible W (run ps a) i = some v) : v = y := by
    have ht := (BirthHistory.atTime_prefix_of_prefix W gs ps a i hps).trans hv
    have h₀ := BirthHistory.visible_before_birth W gs a i k hearlier ps.length hpk hps.length_le v ht
    exact Option.some.inj (h₀.symm.trans hy)
  have source_birth (ps : List (Circuit.Gate n)) (hps : ps.IsPrefix gs) (j : Fin n)
      (hv : visible W (run ps a) j = some f) :
      ∃ p ∈ occurrences W gs a, atTime W gs a (p.1 + 1) p.2 = some f := by
    obtain ⟨suffix, hsuffix⟩ := hps
    obtain ⟨l, hl, _, hv⟩ := BirthHistory.prefix_value_has_birth W ps suffix a j f hv (hfinit j)
    exact ⟨(l, j), by simpa only [hsuffix] using hl, by simpa only [hsuffix] using hv⟩
  obtain ⟨pre, c, t, hct, post, heq, hk, hi, hgood⟩ :=
    BadOccurrences.nonbad_birth B W hW gs a ha (Matching.empty n) k i hb hbad
  have hpre : pre.IsPrefix gs := ⟨.CX c t hct :: post, heq.symm⟩
  have ha' := SymplecticCircuit.run_symplectic B pre a ha
  have hout : visible W (CX c t (run pre a)) i = some q := by
    simpa only [heq, hk, BirthHistory.atTime_after, applyGate] using hnew
  rcases hgood with hT | ⟨_, hm⟩
  · have hbefore := PairInventory.before_two B W hW _ ha' c t hct (by rw [hT]; rfl)
    have hvis : (visible W (run pre a) i).isSome = true := by
      rcases hi with rfl | rfl
      · exact hbefore.1
      · exact hbefore.2
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hvis
    have huy := initial_on_prefix pre hpre (by omega) u hu
    have hsource := MissingParity.T_source B W hW _ ha' c t i hct hT hi y f q
      (hu.trans (congrArg some huy)) hout hq hq_y
    rcases hsource with hc | ht
    · obtain ⟨p, hp, hv⟩ := source_birth pre hpre c hc
      exact ⟨p, hp, Or.inl hv⟩
    · obtain ⟨p, hp, hv⟩ := source_birth pre hpre t ht
      exact ⟨p, hp, Or.inl hv⟩
  · obtain ⟨ps, death, middle, partner, u, b, hp, hpartner, hu, hb', hspan, hlt⟩ :=
      MissingParity.return_origin B W hW pre a ha c t i hct hm hi q hout
    have hps : ps.IsPrefix gs := by
      refine ⟨death :: (middle ++ .CX c t hct :: post), ?_⟩
      simp [heq, hp, List.append_assoc]
    have huy := initial_on_prefix ps hps (by omega) u hu
    have hq0 : q ≠ 0 := ((WireGeometry.visible_spec B W hW _
      (SymplecticCircuit.CX_symplectic B _ ha' c t hct) i q).mp hout).1
    rw [huy] at hspan
    rcases MissingParity.partner_choice y b f q hq hspan hq0 hq_y with hbf | hbq
    · obtain ⟨p, hp, hv⟩ := source_birth ps hps partner (hb'.trans (congrArg some hbf))
      exact ⟨p, hp, Or.inl hv⟩
    · obtain ⟨suffix, hsuffix⟩ := hps
      have hvalue : visible W (run ps a) partner = some q := hb'.trans (congrArg some hbq)
      obtain ⟨l, hl, _, hv⟩ := BirthHistory.prefix_value_has_birth W ps suffix a partner q hvalue (hinit partner)
      exact ⟨(l, partner), by simpa only [hsuffix] using hl,
        Or.inr ⟨by simpa only [hsuffix] using hv, hpartner⟩⟩

/-- A missing-parity recorder with a good first designated birth can be charged
to an undesignated birth. Its source has at most two recorder coordinates. -/
theorem source_charge (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (gs : List (Circuit.Gate n)) (final : Fin r → Fin n) (time : Fin r → Nat)
    (hdv : ∀ a, atTime (StandardSpace.initialW n) gs (standard n) (time a + 1) (final a) =
      some (output label X a))
    (a : Fin r)
    (hmissing : ∀ s ≤ gs.length, ∀ i, atTime (StandardSpace.initialW n) gs (standard n) s i ≠
      some (parity label (X a)))
    (hb : (time a, final a) ∈ occurrences (StandardSpace.initialW n) gs (standard n))
    (hearlier : ∀ l < time a, (l, final a) ∉ occurrences (StandardSpace.initialW n) gs (standard n))
    (hbad : (time a, final a) ∉ BadOccurrences.badOccurrences (StandardSpace.initialW n) gs
      (standard n) (Matching.empty n)) :
    ∃ p ∈ RecorderCharges.undesignated (StandardSpace.initialW n) gs (standard n) final time,
      ∃ b, atTime (StandardSpace.initialW n) gs (standard n) (p.1 + 1) p.2 = some b ∧
        Source label X final a b := by
  have hfinit (j : Fin n) : (standard n).x j ≠ parity label (X a) := by
    simpa only [atTime, List.take_zero, SymplecticCircuit.run, CircuitLedger.initial_visible,
      ne_eq, Option.some.injEq] using hmissing 0 (Nat.zero_le _) j
  have hinit (a : Fin r) (j : Fin n) :
      visible (StandardSpace.initialW n) (standard n) j ≠ some (output label X a) := by
    simpa only [CircuitLedger.initial_visible, ne_eq, Option.some.injEq] using
      RecorderVectors.output_not_initial label X a j
  have hshiftinit (j : Fin n) : visible (StandardSpace.initialW n) (standard n) j ≠
      some (output label X a + (standard n).x (final a)) := by
    simpa only [CircuitLedger.initial_visible, ne_eq, Option.some.injEq] using
      shifted_not_initial label X a (final a) hfinit j
  obtain ⟨p, hp, hv⟩ := classify_source (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) gs (standard n) (StandardSpace.standard_symplectic n)
    (final a) (time a) ((standard n).x (final a))
    (output label X a + (standard n).x (final a)) (output label X a)
    (CircuitLedger.initial_visible n _)
    (by rw [add_left_comm, double, add_zero]) (hinit a) hshiftinit hb (hdv a) hearlier hbad
  rcases hv with hshift | ⟨hq, hwire⟩
  · have hne : final a ≠ recorder label a := by
      intro he
      have hs : output label X a + (standard n).x (final a) = parity label (X a) := by
        rw [he, output, add_right_comm, double, zero_add]
      have hlt := BirthOccurrences.occurrence_time_lt _ _ _ _ hp
      exact hmissing (p.1 + 1) (by omega) p.2 (by simpa only [hs] using hshift)
    refine ⟨p, Finset.mem_sdiff.mpr ⟨hp, ?_⟩, _, hshift, Or.inr ⟨hne, rfl⟩⟩
    intro hdes
    obtain ⟨b, _, he⟩ := Finset.mem_image.mp hdes
    have hh := hdv b
    rw [show time b = p.1 from congrArg Prod.fst he,
      show final b = p.2 from congrArg Prod.snd he] at hh
    exact shifted_ne_output label X a b (final a) (Option.some.inj (hshift.symm.trans hh))
  · refine ⟨p, Finset.mem_sdiff.mpr ⟨hp, ?_⟩, _, hq, Or.inl rfl⟩
    intro hdes
    obtain ⟨b, _, he⟩ := Finset.mem_image.mp hdes
    have hh := hdv b
    rw [show time b = p.1 from congrArg Prod.fst he,
      show final b = p.2 from congrArg Prod.snd he] at hh
    have hab := RecorderVectors.output_injective label X (Option.some.inj (hq.symm.trans hh))
    exact hwire (by simpa only [hab] using (congrArg Prod.snd he).symm)

/-- The displaced-recorder estimate: one excess birth for an earlier birth on
the final wire, at most two per historical source, and exceptional births. -/
theorem count_bound (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (gs : List (Circuit.Gate n)) (final : Fin r → Fin n) (hr : Function.Injective final)
    (hout : ∀ a, visible (StandardSpace.initialW n) (run gs (standard n)) (final a) =
      some (output label X a))
    (f : Space n)
    (hmissing : ∀ s ≤ gs.length, ∀ i, atTime (StandardSpace.initialW n) gs (standard n) s i ≠ some f) :
    (Finset.univ.filter (fun a => parity label (X a) = f)).card ≤
      3 * (CircuitLedger.totalBirths (StandardSpace.initialW n) gs (standard n) - r) +
      (BadOccurrences.badOccurrences (StandardSpace.initialW n) gs (standard n) (Matching.empty n)).card := by
  classical
  let W := StandardSpace.initialW n
  let initial := standard n
  obtain ⟨time, htime, hd, hdv, _⟩ := BirthOccurrences.designated_births W gs initial final hr
    (output label X) hout (fun a => by
      simpa only [W, initial, CircuitLedger.initial_visible, ne_eq, Option.some.injEq] using
        RecorderVectors.output_not_initial label X a (final a))
  let early := RecorderCharges.earlier W gs initial final time
  let bad := BadOccurrences.badOccurrences W gs initial (Matching.empty n)
  let badRec := Finset.univ.filter (fun a => (time a, final a) ∈ bad)
  let missing := Finset.univ.filter (fun a => parity label (X a) = f)
  let good := missing \ (early ∪ badRec)
  let excess := RecorderCharges.undesignated W gs initial final time
  have hex (a : ↥good) : ∃ p ∈ excess, ∃ b,
      atTime W gs initial (p.1 + 1) p.2 = some b ∧ Source label X final a b := by
    have ha := Finset.mem_sdiff.mp a.property
    have haf : parity label (X a) = f := (Finset.mem_filter.mp ha.1).2
    have he : a.val ∉ early := fun h => ha.2 (Finset.mem_union_left _ h)
    have hb : (time a, final a) ∉ bad := fun h => ha.2 (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    apply source_charge label X gs final time hdv a
      (by simpa only [haf] using hmissing) (hd a) _ hb
    intro l hl hocc
    exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l, hl, hocc⟩⟩)
  choose charge hcharge value hvalue hsource using hex
  have hgood : good.card ≤ 2 * excess.card := by
    by_contra h
    have hlarge : excess.card * 2 < (Finset.univ : Finset ↥good).card := by
      simpa only [Finset.card_univ, Fintype.card_coe, Nat.mul_comm] using Nat.lt_of_not_ge h
    obtain ⟨p, _, hfiber⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := Finset.univ) (f := charge) (fun a _ => hcharge a) hlarge
    let fiber := Finset.univ.filter (fun a : ↥good => charge a = p)
    change 2 < fiber.card at hfiber
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < fiber.card by omega)
    have hap : charge a = p := (Finset.mem_filter.mp ha).2
    have hsupport (c : ↥good) (hc : c ∈ fiber) :
        recorder label c.val ∈ ({recorder label a.val, final a.val} : Finset (Fin n)) := by
      have hcp : charge c = p := (Finset.mem_filter.mp hc).2
      have hval : value a = value c := Option.some.inj
        ((hvalue a).symm.trans (by simpa only [hap, hcp] using hvalue c))
      have hh := source_support label X final a c (value a) (hsource a)
        (by simpa only [hval] using hsource c)
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hh
    have hcard := Finset.card_le_card_of_injOn (fun c : ↥good => recorder label c.val)
      hsupport (fun a _ b _ h => Subtype.ext (RecorderVectors.recorder_injective label h))
    have htwo : ({recorder label a.val, final a.val} : Finset (Fin n)).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega
  have hbad : badRec.card ≤ bad.card := by
    apply Finset.card_le_card_of_injOn (fun a => (time a, final a))
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
    · exact htime.injOn
  have hsub : missing ⊆ good ∪ (early ∪ badRec) := by
    intro a ha
    by_cases h : a ∈ early ∪ badRec
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, h⟩)
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le good (early ∪ badRec)
  have hv := Finset.card_union_le early badRec
  have he := RecorderCharges.earlier_count_le_excess W gs initial final hr time hd
  have hx := RecorderCharges.undesignated_card W gs initial final hr time hd
  change early.card ≤ _ at he
  change excess.card = _ at hx
  change missing.card ≤ 3 * (CircuitLedger.totalBirths W gs initial - r) + bad.card
  omega

/-- The displaced-recorder estimate `3E + 3M + 4Z`. -/
theorem missing_bound (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (gs : List (Circuit.Gate n)) (final : Fin r → Fin n) (hr : Function.Injective final)
    (hout : ∀ a, visible (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) (final a) = some (output label X a))
    (f : Space n)
    (hmissing : ∀ s ≤ gs.length, ∀ i, atTime (StandardSpace.initialW n) gs (standard n) s i ≠ some f) :
    (Finset.univ.filter (fun a => parity label (X a) = f)).card ≤
      3 * (CircuitLedger.totalBirths (StandardSpace.initialW n) gs (standard n) - r) +
      Ledger.markCharge (CircuitLedger.trace (StandardSpace.initialW n) gs (standard n)) := by
  have hout' := hout
  simp only [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity] at hout'
  exact (count_bound label X gs final hr hout' f hmissing).trans
    (Nat.add_le_add_left (BadOccurrences.actual_bad_card_sharp gs) _)

/-- The factor-six bound when every final qubit represents a vector. -/
theorem missing_cost_bound_of_final_count (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (gs : List (Circuit.Gate n)) (final : Fin r → Fin n) (hr : Function.Injective final)
    (hout : ∀ a, visible (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) (final a) = some (output label X a))
    (hfinal : Observation.count (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) = n)
    (f : Space n)
    (hmissing : ∀ s ≤ gs.length, ∀ i, atTime (StandardSpace.initialW n) gs (standard n) s i ≠ some f) :
    (Finset.univ.filter (fun a => parity label (X a) = f)).card ≤ 6 * (Circuit.cost gs - r) := by
  have hout' := hout
  simp only [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity] at hout'
  have hc := missing_bound label X gs final hr hout f hmissing
  have hb := PairAccounting.actual_markCharge_bound gs hfinal
  have hl := CircuitLedger.actual_birth_bound gs hfinal
  have hR := BirthOccurrences.recorder_count_le_births (StandardSpace.initialW n) gs
    (standard n) final hr (output label X) hout' (fun a => by
      simpa only [CircuitLedger.initial_visible, ne_eq, Option.some.injEq] using
        RecorderVectors.output_not_initial label X a (final a))
  omega

/-- In particular, displaced outputs obey `6(L-R)` for linear targets. -/
theorem missing_cost_bound (label : Wire d r ≃ Fin n) (X : Fin r → Fin d → F)
    (gs : List (Circuit.Gate n)) (final : Fin r → Fin n) (hr : Function.Injective final)
    (hout : ∀ a, visible (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) (final a) = some (output label X a))
    (hlinear : ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false)
    (f : Space n)
    (hmissing : ∀ s ≤ gs.length, ∀ i, atTime (StandardSpace.initialW n) gs (standard n) s i ≠ some f) :
    (Finset.univ.filter (fun a => parity label (X a) = f)).card ≤ 6 * (Circuit.cost gs - r) := by
  apply missing_cost_bound_of_final_count label X gs final hr hout ?_ f hmissing
  apply Observation.count_of_all_x (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _ (StandardSpace.actual_run_symplectic gs)
  intro i
  simp [StandardSpace.initialW_mem, StandardSpace.fieldRows, hlinear, LocalChart.bit]

end CliffordSynthesis.DisplacedRecorders
