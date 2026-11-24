/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.BadOccurrences
public import CliffordSynthesis.RecorderCharges

/-!
# Missing Parity

The missing-parity bound for recorder outputs. Appearances (`births`) are
charged using the circuit's gate sequence, listed-pair origins, and occurrence
sets.
-/

public section

namespace CliffordSynthesis.MissingParity

open LinearMap (BilinForm)
open Planes (F plane)
open SymplecticCircuit (Rows IsSymplectic CX run applyGate)
open Observation (visible)
open PairInventory (event evolve)
open BirthOccurrences (Occurrence occurrences atTime)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

attribute [local instance] Classical.propDecidable

/-- At a T birth y ↦ y+f, the other participating wire carries f. -/
theorem T_source (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (a : Rows n V) (ha : IsSymplectic B a) (c t i : Fin n) (hct : c ≠ t)
    (he : event W a c t = .T) (hi : i = c ∨ i = t) (y f q : V)
    (hbefore : visible W a i = some y) (hafter : visible W (CX c t a) i = some q)
    (hq : q = y + f) (hqy : q ≠ y) : visible W a c = some f ∨ visible W a t = some f := by
  have hs := CircuitLedger.classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
  change (event W a c t).before = _ ∧ (event W a c t).after = _ ∧ (event W a c t).births = _ at hs
  rw [he] at hs
  have hsig : Observation.signature W a (CX c t a) c t = (2, 2, 1) :=
    Prod.ext hs.1.symm (Prod.ext hs.2.1.symm hs.2.2.symm)
  obtain ⟨u, v, hu, hv, hadd⟩ := Observation.cnot_rowAddition B W hW a ha c t hct hsig
  rcases hi with rfl | rfl
  · have huy : u = y := Option.some.inj (hu.symm.trans hbefore)
    rcases hadd with ⟨hu', _⟩ | ⟨hu', _⟩
    · have hqu : q = u := Option.some.inj (hafter.symm.trans hu')
      exact False.elim (hqy (hqu.trans huy))
    · have huv : u + v = y + f := (Option.some.inj (hu'.symm.trans hafter)).trans hq
      have hvf : v = f := add_left_cancel (by simpa only [huy] using huv)
      exact Or.inr (hv.trans (congrArg some hvf))
  · have hvy : v = y := Option.some.inj (hv.symm.trans hbefore)
    rcases hadd with ⟨_, hv'⟩ | ⟨_, hv'⟩
    · have huv : u + v = y + f := (Option.some.inj (hv'.symm.trans hafter)).trans hq
      have huf : u = f := add_left_cancel (by simpa only [hvy, add_comm u y] using huv)
      exact Or.inl (hu.trans (congrArg some huf))
    · have hqv : q = v := Option.some.inj (hafter.symm.trans hv')
      exact False.elim (hqy (hqv.trans hvy))

theorem partner_choice (y b f q : V) (hq : q = y + f) (hp : q ∈ plane y b)
    (hq0 : q ≠ 0) (hqy : q ≠ y) : b = f ∨ b = q := by
  rcases (Planes.mem_plane_iff y b q).mp hp with hz | hy | hb | hyb
  · exact False.elim (hq0 hz)
  · exact False.elim (hqy hy)
  · exact Or.inr hb.symm
  · exact Or.inl (add_left_cancel (hyb.symm.trans hq))

/-- Orient the historical span around either endpoint of a returning pair. -/
theorem return_origin (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (c t i : Fin n) (hct : c ≠ t) (hm : (evolve W gs a (Matching.empty n)).mate c = some t)
    (hi : i = c ∨ i = t) (q : V) (hq : visible W (CX c t (run gs a)) i = some q) :
    ∃ pre g post partner u b, gs = pre ++ g :: post ∧ partner ≠ i ∧
      visible W (run pre a) i = some u ∧ visible W (run pre a) partner = some b ∧
      q ∈ plane u b ∧ pre.length < gs.length := by
  obtain ⟨pre, g, post, u, v, heq, _, hu, hv, hs, hlt⟩ := PairOrigins.origin_span B W hW gs a ha c t hm
  have hafter := SymplecticCircuit.CX_symplectic B _ (SymplecticCircuit.run_symplectic B gs a ha) c t hct
  have hq' := (WireGeometry.visible_spec B W hW _ hafter i q).mp hq
  have hs' : W ⊓ WireGeometry.joint (CX c t (run gs a)) c t = plane u v := by
    rw [WireGeometry.CX_joint _ c t hct, hs]
  have hqin : q ∈ plane u v := by
    rw [← hs']
    refine ⟨hq'.2.1, ?_⟩
    rcases hi with rfl | rfl
    · exact Submodule.mem_sup_left hq'.2.2
    · exact Submodule.mem_sup_right hq'.2.2
  rcases hi with rfl | rfl
  · exact ⟨pre, g, post, t, u, v, heq, Ne.symm hct, hu, hv, hqin, hlt⟩
  · refine ⟨pre, g, post, c, v, u, heq, hct, hv, hu, ?_, hlt⟩
    simpa only [Planes.hadamard_plane] using hqin

/-- A missing-parity recorder whose designated birth has neither an earlier
own-wire birth nor an exceptional origin must have a birth of its output on
a different wire. This is the substantive classification in the charging proof. -/
theorem classify_missing (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (i : Fin n) (k : Nat) (y f q : V) (hy : visible W a i = some y) (hq : q = y + f)
    (hinit : ∀ j, visible W a j ≠ some q)
    (hmissing : ∀ s ≤ gs.length, ∀ j, atTime W gs a s j ≠ some f)
    (hb : (k, i) ∈ occurrences W gs a) (hnew : atTime W gs a (k + 1) i = some q)
    (hearlier : ∀ l < k, (l, i) ∉ occurrences W gs a)
    (hbad : (k, i) ∉ BadOccurrences.badOccurrences W gs a (Matching.empty n)) :
    ∃ p ∈ occurrences W gs a, atTime W gs a (p.1 + 1) p.2 = some q ∧ p.2 ≠ i := by
  have hq_y : q ≠ y := by
    intro h
    exact hinit i (by simpa only [h] using hy)
  have initial_on_prefix (ps : List (Circuit.Gate n)) (hps : ps.IsPrefix gs)
      (hpk : ps.length ≤ k) (v : V) (hv : visible W (run ps a) i = some v) : v = y := by
    have ht : atTime W gs a ps.length i = some v :=
      (BirthHistory.atTime_prefix_of_prefix W gs ps a i hps).trans hv
    have h₀ := BirthHistory.visible_before_birth W gs a i k hearlier ps.length hpk hps.length_le v ht
    exact Option.some.inj (h₀.symm.trans hy)
  obtain ⟨pre, c, t, hct, post, heq, hk, hi, hgood⟩ :=
    BadOccurrences.nonbad_birth B W hW gs a ha (Matching.empty n) k i hb hbad
  have hpre : pre.IsPrefix gs := ⟨.CX c t hct :: post, heq.symm⟩
  have ha' := SymplecticCircuit.run_symplectic B pre a ha
  have hout : visible W (CX c t (run pre a)) i = some q := by
    simpa only [heq, hk, BirthHistory.atTime_after, applyGate] using hnew
  rcases hgood with hT | ⟨hU, hm⟩
  · have hbefore := PairInventory.before_two B W hW _ ha' c t hct (by rw [hT]; rfl)
    have hvis : (visible W (run pre a) i).isSome = true := by
      rcases hi with rfl | rfl
      · exact hbefore.1
      · exact hbefore.2
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hvis
    have huy := initial_on_prefix pre hpre (by omega) u hu
    have hsource := T_source B W hW _ ha' c t i hct hT hi y f q
      (hu.trans (congrArg some huy)) hout hq hq_y
    rcases hsource with hsource | hsource
    · exact False.elim (hmissing pre.length hpre.length_le c
        ((BirthHistory.atTime_prefix_of_prefix W gs pre a c hpre).trans hsource))
    · exact False.elim (hmissing pre.length hpre.length_le t
        ((BirthHistory.atTime_prefix_of_prefix W gs pre a t hpre).trans hsource))
  · obtain ⟨ps, death, middle, partner, u, b, hp, hpartner, hu, hb', hspan, hlt⟩ :=
      return_origin B W hW pre a ha c t i hct hm hi q hout
    have hps : ps.IsPrefix gs := by
      refine ⟨death :: (middle ++ .CX c t hct :: post), ?_⟩
      simp [heq, hp, List.append_assoc]
    have huy := initial_on_prefix ps hps (by omega) u hu
    have hq0 : q ≠ 0 := ((WireGeometry.visible_spec B W hW _
      (SymplecticCircuit.CX_symplectic B _ ha' c t hct) i q).mp hout).1
    rw [huy] at hspan
    rcases partner_choice y b f q hq hspan hq0 hq_y with hbf | hbq
    · have hvf : atTime W gs a ps.length partner = some f :=
        (BirthHistory.atTime_prefix_of_prefix W gs ps a partner hps).trans (hb'.trans (congrArg some hbf))
      exact False.elim (hmissing ps.length hps.length_le partner hvf)
    · obtain ⟨suffix, hsuffix⟩ := hps
      have hvalue : visible W (run ps a) partner = some q := hb'.trans (congrArg some hbq)
      obtain ⟨l, hl, _, hv⟩ := BirthHistory.prefix_value_has_birth W ps suffix a partner q hvalue (hinit partner)
      refine ⟨(l, partner), ?_, ?_, hpartner⟩
      · simpa only [hsuffix] using hl
      · simpa only [hsuffix] using hv

/-- The number of recorders requesting a missing parity is bounded by the two
proved charge classes and the actual exceptional-origin birth occurrences. -/
theorem count_bound {r : Nat} (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (initial : Fin n → V) (hinitial : ∀ i, visible W a i = some (initial i))
    (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (output parity : Fin r → V) (ho : Function.Injective output)
    (heq : ∀ j, output j = initial (recorder j) + parity j)
    (hinit : ∀ j i, visible W a i ≠ some (output j))
    (hout : ∀ j, visible W (run gs a) (recorder j) = some (output j))
    (f : V) (hmissing : ∀ s ≤ gs.length, ∀ i, atTime W gs a s i ≠ some f) :
    (Finset.univ.filter (fun j => parity j = f)).card ≤
      2 * (CircuitLedger.totalBirths W gs a - r) +
      (BadOccurrences.badOccurrences W gs a (Matching.empty n)).card := by
  classical
  obtain ⟨time, htime, hd, hdv, _⟩ := BirthOccurrences.designated_births W gs a recorder hr output hout
    (fun j => hinit j (recorder j))
  let badSet := BadOccurrences.badOccurrences W gs a (Matching.empty n)
  let badRec := Finset.univ.filter (fun j => (time j, recorder j) ∈ badSet)
  have hbadcard : badRec.card ≤ badSet.card := by
    apply Finset.card_le_card_of_injOn (fun j => (time j, recorder j))
    · intro j hj
      simpa [badRec] using hj
    · exact htime.injOn
  have hsub : (Finset.univ.filter (fun j => parity j = f)) ⊆
      (RecorderCharges.earlier W gs a recorder time ∪ RecorderCharges.wrongWire W gs a recorder output) ∪ badRec := by
    intro j hj
    have hjf : parity j = f := by simpa using hj
    by_cases hE : j ∈ RecorderCharges.earlier W gs a recorder time
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hE)
    by_cases hBad : (time j, recorder j) ∈ badSet
    · exact Finset.mem_union_right _ (by simp [badRec, hBad])
    have hnone : ∀ l < time j, (l, recorder j) ∉ occurrences W gs a := by
      intro l hl hb
      exact hE (by simp only [RecorderCharges.earlier, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨l, hl, hb⟩)
    obtain ⟨p, hp, hv, hw⟩ := classify_missing B W hW gs a ha (recorder j) (time j)
      (initial (recorder j)) f (output j) (hinitial _) (by simpa [hjf] using heq j)
      (hinit j) hmissing (hd j) (hdv j) hnone hBad
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    simp only [RecorderCharges.wrongWire, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p, hp, hv, hw⟩
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le
    (RecorderCharges.earlier W gs a recorder time ∪ RecorderCharges.wrongWire W gs a recorder output) badRec
  have h₃ := Finset.card_union_le (RecorderCharges.earlier W gs a recorder time)
    (RecorderCharges.wrongWire W gs a recorder output)
  have hE := RecorderCharges.earlier_count_le_excess W gs a recorder hr time hd
  have hW' := RecorderCharges.wrong_wire_count_le_excess W gs a recorder hr output ho time hd hdv
  dsimp only [badSet] at hbadcard
  omega

/-- The `2E + 3M + 4Z` bound in the original circuit's vector
space. `Ledger.markCharge_eq` identifies the weighted event count. -/
theorem actual_missing_bound {r : Nat} (gs : List (Circuit.Gate n))
    (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (output parity : Fin r → StandardSpace.Space n) (ho : Function.Injective output)
    (heq : ∀ j, output j = (StandardSpace.standard n).x (recorder j) + parity j)
    (hinit : ∀ j i, (StandardSpace.standard n).x i ≠ output j)
    (hout : ∀ j, visible (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) (recorder j) = some (output j))
    (f : StandardSpace.Space n)
    (hmissing : ∀ s ≤ gs.length, ∀ i, atTime (StandardSpace.initialW n) gs (StandardSpace.standard n) s i ≠ some f) :
    (Finset.univ.filter (fun j => parity j = f)).card ≤
      2 * (CircuitLedger.totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n) - r) +
      Ledger.markCharge (CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  have hi : ∀ j i, visible (StandardSpace.initialW n) (StandardSpace.standard n) i ≠ some (output j) := by
    intro j i
    simpa only [CircuitLedger.initial_visible, ne_eq, Option.some.injEq] using hinit j i
  have hout' := hout
  simp only [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity] at hout'
  have hh := count_bound (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) gs _ (StandardSpace.standard_symplectic n)
    (StandardSpace.standard n).x (CircuitLedger.initial_visible n) recorder hr output parity ho heq hi hout' f hmissing
  have hb := BadOccurrences.actual_bad_card_sharp gs
  convert hh.trans (Nat.add_le_add_left hb _) using 1
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The `6(L-R)` bound under the endpoint condition: every
final qubit represents a vector. No particular final row basis is required. -/
theorem actual_missing_cost_bound_of_final_count {r : Nat} (gs : List (Circuit.Gate n))
    (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (output parity : Fin r → StandardSpace.Space n) (ho : Function.Injective output)
    (heq : ∀ j, output j = (StandardSpace.standard n).x (recorder j) + parity j)
    (hinit : ∀ j i, (StandardSpace.standard n).x i ≠ output j)
    (hout : ∀ j, visible (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) (recorder j) = some (output j))
    (hfinal : Observation.count (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) = n)
    (f : StandardSpace.Space n)
    (hmissing : ∀ s ≤ gs.length, ∀ i, atTime (StandardSpace.initialW n) gs (StandardSpace.standard n) s i ≠ some f) :
    (Finset.univ.filter (fun j => parity j = f)).card ≤ 6 * (Circuit.cost gs - r) := by
  have hh := actual_missing_bound gs recorder hr output parity ho heq hinit hout f hmissing
  have hl := CircuitLedger.actual_birth_bound gs hfinal
  have hcharge := PairAccounting.actual_markCharge_bound gs hfinal
  have hout' := hout
  simp only [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity] at hout'
  have hR := BirthOccurrences.recorder_count_le_births (StandardSpace.initialW n) gs
    (StandardSpace.standard n) recorder hr output hout'
    (fun j => by simpa only [CircuitLedger.initial_visible, ne_eq, Option.some.injEq] using hinit j (recorder j))
  omega

/-- The same bound for the linear-output circuits used by the reduction. -/
theorem actual_missing_cost_bound {r : Nat} (gs : List (Circuit.Gate n))
    (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (output parity : Fin r → StandardSpace.Space n) (ho : Function.Injective output)
    (heq : ∀ j, output j = (StandardSpace.standard n).x (recorder j) + parity j)
    (hinit : ∀ j i, (StandardSpace.standard n).x i ≠ output j)
    (hout : ∀ j, visible (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) (recorder j) = some (output j))
    (hlinear : ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false)
    (f : StandardSpace.Space n)
    (hmissing : ∀ s ≤ gs.length, ∀ i, atTime (StandardSpace.initialW n) gs (StandardSpace.standard n) s i ≠ some f) :
    (Finset.univ.filter (fun j => parity j = f)).card ≤ 6 * (Circuit.cost gs - r) := by
  apply actual_missing_cost_bound_of_final_count gs recorder hr output parity ho heq hinit hout ?_ f hmissing
  apply Observation.count_of_all_x (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _ (StandardSpace.actual_run_symplectic gs)
  intro i
  simp [StandardSpace.initialW_mem, StandardSpace.fieldRows, hlinear, LocalChart.bit]

/-- The replication factor in the reduction forces the requested parity to
appear somewhere in the actual circuit history. -/
theorem replication_forces_visible {r m : Nat} (gs : List (Circuit.Gate n))
    (recorder : Fin r → Fin n) (hr : Function.Injective recorder)
    (output parity : Fin r → StandardSpace.Space n) (ho : Function.Injective output)
    (heq : ∀ j, output j = (StandardSpace.standard n).x (recorder j) + parity j)
    (hinit : ∀ j i, (StandardSpace.standard n).x i ≠ output j)
    (hout : ∀ j, visible (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) (recorder j) = some (output j))
    (hlinear : ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false)
    (hbudget : Circuit.cost gs ≤ r + (m - 1)) (f : StandardSpace.Space n)
    (hcopies : 6 * (m - 1) + 1 ≤ (Finset.univ.filter (fun j => parity j = f)).card) :
    ∃ s ≤ gs.length, ∃ i, atTime (StandardSpace.initialW n) gs (StandardSpace.standard n) s i = some f := by
  by_contra h
  push Not at h
  have hh := actual_missing_cost_bound gs recorder hr output parity ho heq hinit hout hlinear f h
  omega

end CliffordSynthesis.MissingParity
