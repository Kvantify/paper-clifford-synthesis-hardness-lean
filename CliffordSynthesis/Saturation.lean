/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.MissingParity

/-!
# SATuration

Globally fresh births exclude hidden-pair returns. Together with a saturated
ledger this forces every paid gate to have the classical row-addition type.
-/

@[expose] public section

namespace CliffordSynthesis.Saturation

open LinearMap (BilinForm)
open Planes (F)
open SymplecticCircuit (Rows IsSymplectic run applyGate CX)
open Observation (visible)
open PairInventory (event evolve)
open BirthOccurrences (occurrences atTime)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

/-- Every birth is absent from every wire at every earlier circuit boundary. -/
def GloballyFresh (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V) : Prop :=
  ∀ k i q, (k, i) ∈ occurrences W gs a → atTime W gs a (k + 1) i = some q →
    ∀ s ≤ k, ∀ j, atTime W gs a s j ≠ some q

theorem fresh_excludes_return (B : BilinForm F V) (W : Submodule F V)
    (hW : Splitting.Isotropic B W) (gs : List (Circuit.Gate n))
    (a : Rows n V) (ha : IsSymplectic B a) (hf : GloballyFresh W gs a)
    (hbad : BadOccurrences.badOccurrences W gs a (Matching.empty n) = ∅)
    (pre post : List (Circuit.Gate n)) (c t : Fin n) (hct : c ≠ t)
    (hgs : gs = pre ++ .CX c t hct :: post) : event W (run pre a) c t ≠ .U := by
  classical
  intro hU
  have ha' := SymplecticCircuit.run_symplectic B pre a ha
  have hb := PairInventory.before_zero B W hW _ ha' c t hct (by rw [hU]; rfl)
  have hv := PairInventory.after_two B W hW _ ha' c t hct (by rw [hU]; rfl)
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hv.1
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hv.2
  have hpw : c ∈ BirthOccurrences.stepWires W (run pre a) (CX c t (run pre a)) := by
    simp [BirthOccurrences.mem_stepWires, hb.1, hp]
  have hqw : t ∈ BirthOccurrences.stepWires W (run pre a) (CX c t (run pre a)) := by
    simp [BirthOccurrences.mem_stepWires, hb.2, hq]
  have notbad : c ∉ BadOccurrences.badWires W (run pre a)
      (evolve W pre a (Matching.empty n)) (.CX c t hct) := by
    rw [← BadOccurrences.mem_at_prefix W pre (.CX c t hct) post a (Matching.empty n) c,
      ← hgs, hbad]
    simp
  have hgood : BadOccurrences.Good W (run pre a) (evolve W pre a (Matching.empty n)) c t := by
    by_contra hg
    exact notbad (by simpa [BadOccurrences.badWires, hg, applyGate] using hpw)
  have hm : (evolve W pre a (Matching.empty n)).mate c = some t := by
    simpa [BadOccurrences.Good, hU] using hgood
  have born (i : Fin n) (w : V) (hbefore : visible W (run pre a) i = none)
      (hafter : visible W (CX c t (run pre a)) i = some w) :
      (pre.length, i) ∈ occurrences W gs a ∧ atTime W gs a (pre.length + 1) i = some w := by
    have hh : atTime W gs a (pre.length + 1) i = some w := by
      simpa only [hgs, BirthHistory.atTime_after, applyGate] using hafter
    refine ⟨(BirthOccurrences.occurrence_iff W gs a pre.length i).mpr ⟨?_, ?_, ?_⟩, hh⟩
    · simp only [hgs, List.length_append, List.length_cons]; omega
    · simp [hh]
    · rw [hh, hgs, BirthHistory.atTime_prefix, hbefore]
      exact Option.some_ne_none _
  have hpb := born c p hb.1 hp
  have hqb := born t q hb.2 hq
  obtain ⟨ps, g, middle, u, v, hpre, hu, hv, hps, hqs, hlt⟩ :=
    PairOrigins.return_span B W hW pre a ha c t hct hm p q hp hq
  have hprefix : ps.IsPrefix gs := by
    refine ⟨g :: (middle ++ .CX c t hct :: post), ?_⟩
    simp [hgs, hpre, List.append_assoc]
  have hpu : p ≠ u := by
    intro h
    exact hf _ c p hpb.1 hpb.2 ps.length (by omega) c
      ((BirthHistory.atTime_prefix_of_prefix W gs ps a c hprefix).trans (by simpa [h] using hu))
  have hpv : p ≠ v := by
    intro h
    exact hf _ c p hpb.1 hpb.2 ps.length (by omega) t
      ((BirthHistory.atTime_prefix_of_prefix W gs ps a t hprefix).trans (by simpa [h] using hv))
  have hqu : q ≠ u := by
    intro h
    exact hf _ t q hqb.1 hqb.2 ps.length (by omega) c
      ((BirthHistory.atTime_prefix_of_prefix W gs ps a c hprefix).trans (by simpa [h] using hu))
  have hqv : q ≠ v := by
    intro h
    exact hf _ t q hqb.1 hqb.2 ps.length (by omega) t
      ((BirthHistory.atTime_prefix_of_prefix W gs ps a t hprefix).trans (by simpa [h] using hv))
  have ha'' := SymplecticCircuit.CX_symplectic B _ ha' c t hct
  have hp0 := ((WireGeometry.visible_spec B W hW _ ha'' c p).mp hp).1
  have hq0 := ((WireGeometry.visible_spec B W hW _ ha'' t q).mp hq).1
  exact WireGeometry.visible_distinct B W hW _ ha'' c t hct p q hp hq
    (Planes.no_two_fresh u v p q hps hqs hp0 hq0 hpu hpv hqu hqv)

/-- A property of every paid prefix is a property of every constructed event. -/
theorem trace_of_prefixes (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V)
    (P : Ledger.Event → Prop)
    (h : ∀ pre post c t (hct : c ≠ t), gs = pre ++ .CX c t hct :: post → P (event W (run pre a) c t)) :
    ∀ e ∈ CircuitLedger.trace W gs a, P e := by
  induction gs generalizing a with
  | nil => simp [CircuitLedger.trace]
  | cons g gs ih =>
    have ht : ∀ e ∈ CircuitLedger.trace W gs (applyGate g a), P e := by
      apply ih
      intro pre post c t hct heq
      exact h (g :: pre) post c t hct (by simp [heq])
    cases g with
    | H q => exact ht
    | S q => exact ht
    | CX c t hct =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact h [] gs c t hct rfl
      · exact ht e he

theorem births_le_length_without_U (es : List Ledger.Event) (hu : Ledger.Event.U ∉ es) :
    Ledger.births es ≤ es.length := by
  induction es with
  | nil => exact Nat.le_refl 0
  | cons e es ih =>
    have he : e ≠ .U := by intro h; exact hu (by simp [h])
    have ht : Ledger.Event.U ∉ es := fun h => hu (List.mem_cons_of_mem _ h)
    have hb : e.births ≤ 1 := by cases e <;> simp_all [Ledger.Event.births]
    have hi := ih ht
    simp only [Ledger.births, List.length_cons]
    omega

theorem saturated_trace_T (es : List Ledger.Event) (hs : Ledger.births es = es.length)
    (hh : Ledger.exceptional es = 0) (hu : Ledger.Event.U ∉ es) : ∀ e ∈ es, e = .T := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have hut : Ledger.Event.U ∉ es := fun h => hu (List.mem_cons_of_mem _ h)
    have hb := births_le_length_without_U es hut
    have hh' : e.exceptional = 0 ∧ Ledger.exceptional es = 0 := by
      simpa only [Ledger.exceptional, Nat.add_eq_zero_iff] using hh
    have he : e = .T := by
      cases e <;> simp_all [Ledger.births, Ledger.Event.births, Ledger.Event.exceptional]
    subst e
    have hst : Ledger.births es = es.length := by
      simpa only [Ledger.births, Ledger.Event.births, List.length_cons, Nat.add_comm 1, Nat.add_right_cancel_iff] using hs
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact ih hst hh'.2 hut e he

/-- For actual linear-output circuits, saturation and global freshness force
every paid event to be an ordinary addition of visible rows. -/
theorem actual_all_T (gs : List (Circuit.Gate n))
    (hlinear : ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false)
    (hs : CircuitLedger.totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n) = Circuit.cost gs)
    (hf : GloballyFresh (StandardSpace.initialW n) gs (StandardSpace.standard n)) :
    ∀ e ∈ CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n), e = .T := by
  have hl := (CircuitLedger.actual_linear_birth_bound gs hlinear).2
  have hh : Ledger.exceptional (CircuitLedger.trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) = 0 := by
    omega
  have hb := BadOccurrences.actual_bad_card gs
  have hbad : BadOccurrences.badOccurrences (StandardSpace.initialW n) gs
      (StandardSpace.standard n) (Matching.empty n) = ∅ := by
    apply Finset.card_eq_zero.mp
    omega
  have hno := trace_of_prefixes (StandardSpace.initialW n) gs (StandardSpace.standard n)
    (fun e => e ≠ .U) (fresh_excludes_return (StandardSpace.form n) (StandardSpace.initialW n)
      (StandardSpace.initialW_isotropic n) gs _ (StandardSpace.standard_symplectic n) hf hbad)
  apply saturated_trace_T
  · rw [CircuitLedger.trace_births _ _ (StandardSpace.initialW_isotropic n) _ _
      (StandardSpace.standard_symplectic n), CircuitLedger.trace_length, hs]
  · exact hh
  · exact fun h => hno .U h rfl

end CliffordSynthesis.Saturation
