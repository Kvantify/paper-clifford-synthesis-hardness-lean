/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordFrontier.FullCertificates

/-!
# Full Membership

NP membership for dense phase-free tableau synthesis.
-/

public section

namespace CliffordFrontier

open Cslib.Complexity CliffordSynthesis
open TwoQubit (StepWithSwap)

namespace FullVerifier

private theorem no_swaps {n : Nat} (Γ : Set TwoQubit.Gate) (gs : List (StepWithSwap n))
    (ha : ∀ g ∈ gs, Allowed Γ false g) :
    ∃ cs : List (TwoQubit.Step n), cs.map StepWithSwap.gate = gs := by
  induction gs with
  | nil => exact ⟨[], rfl⟩
  | cons g gs ih =>
    obtain ⟨cs, rfl⟩ := ih (fun g hg => ha g (List.mem_cons_of_mem _ hg))
    cases g with
    | gate g => exact ⟨g :: cs, rfl⟩
    | swap i j => exact Bool.noConfusion (ha _ List.mem_cons_self)

private theorem gateFamily_eq (Γ : Set TwoQubit.Gate) :
    fullGateFamilySynthesis Γ = language Γ false := by
  ext out
  change TwoQubit.SynthesizesFrom Γ _ _ ↔ out ∈ language Γ false
  constructor
  · rintro ⟨cs, ha, hc, hr⟩
    exact ⟨cs.map StepWithSwap.gate, (allowed_embed Γ false cs).mpr ha,
      by rwa [StepWithSwap.cost_gates], by rwa [StepWithSwap.run_gates]⟩
  · rintro ⟨gs, ha, hc, hr⟩
    obtain ⟨cs, rfl⟩ := no_swaps Γ gs ha
    exact ⟨cs, (allowed_embed Γ false cs).mp ha, by rwa [StepWithSwap.cost_gates] at hc,
      by rwa [StepWithSwap.run_gates] at hr⟩

private theorem gateFamilyFreeSwaps_eq (Γ : Set TwoQubit.Gate) :
    fullGateFamilySynthesisWithFreeSwaps Γ = language Γ true := by
  ext out
  change TwoQubit.SynthesizesFromWithFreeSwaps Γ _ _ ↔ out ∈ language Γ true
  have h (g : StepWithSwap (decodeFull out).qubits) :
      g.allowed Γ ↔ Allowed Γ true g := by
    cases g <;> simp [StepWithSwap.allowed, Allowed]
  constructor
  · rintro ⟨gs, ha, hc, hr⟩
    exact ⟨gs, fun g hg => (h g).mp (ha g hg), hc, hr⟩
  · rintro ⟨gs, ha, hc, hr⟩
    exact ⟨gs, fun g hg => (h g).mpr (ha g hg), hc, hr⟩

private def cnotFamily : Set TwoQubit.Gate := {TwoQubit.cnotGate}

private theorem cnot_supports : TwoQubit.SupportsCNOT cnotFamily :=
  ⟨TwoQubit.cnotGate, rfl, TwoQubit.cnot_locallyCNOT⟩

private def embedCnot {n : Nat} : FreeSwaps.Step n → StepWithSwap n
  | .gate g => .gate (TwoQubit.ofGate g)
  | .swap i j => .swap i j

private theorem embedCnot_run {n : Nat} (cs : List (FreeSwaps.Step n)) (a : Circuit.Tableau n) :
    StepWithSwap.run (cs.map embedCnot) a = FreeSwaps.execute cs a := by
  induction cs generalizing a with
  | nil => rfl
  | cons g cs ih =>
    cases g with
    | gate g =>
      change StepWithSwap.run (cs.map embedCnot) (TwoQubit.applyStep (TwoQubit.ofGate g) a) = _
      rw [TwoQubit.ofGate_apply, ih]
      rfl
    | swap i j => exact ih _

private theorem embedCnot_cost {n : Nat} (cs : List (FreeSwaps.Step n)) :
    StepWithSwap.cost (cs.map embedCnot) = FreeSwaps.count cs := by
  induction cs with
  | nil => rfl
  | cons g cs ih =>
    cases g with
    | gate g => cases g <;> simp [embedCnot, StepWithSwap.cost, FreeSwaps.count,
        TwoQubit.ofGate, TwoQubit.paid, Circuit.paid, ih]
    | swap i j => exact ih

private theorem embedCnot_allowed {n : Nat} (cs : List (FreeSwaps.Step n)) :
    ∀ g ∈ cs.map embedCnot, Allowed cnotFamily true g := by
  intro g hg
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg
  cases g with
  | gate g => cases g <;> simp [Allowed, embedCnot, TwoQubit.ofGate, TwoQubit.Allowed, cnotFamily]
  | swap i j => rfl

private theorem invertCnot {n : Nat} (g : TwoQubit.Step n) (h : TwoQubit.Allowed cnotFamily g) :
    ∃ c : Circuit.Gate n, TwoQubit.ofGate c = g := by
  cases g with
  | H i => exact ⟨.H i, rfl⟩
  | S i => exact ⟨.S i, rfl⟩
  | two c t hct m =>
    change m = TwoQubit.cnotGate at h
    subst m
    exact ⟨.CX c t hct, rfl⟩

private theorem invertCnotList {n : Nat} (gs : List (TwoQubit.Step n))
    (ha : ∀ g ∈ gs, TwoQubit.Allowed cnotFamily g) :
    ∃ cs : List (Circuit.Gate n), cs.map TwoQubit.ofGate = gs := by
  induction gs with
  | nil => exact ⟨[], rfl⟩
  | cons g gs ih =>
    obtain ⟨cs, rfl⟩ := ih (fun g hg => ha g (List.mem_cons_of_mem _ hg))
    obtain ⟨c, rfl⟩ := invertCnot g (ha g List.mem_cons_self)
    exact ⟨c :: cs, rfl⟩

private theorem invertCnotFreeSwaps {n : Nat} (gs : List (StepWithSwap n))
    (ha : ∀ g ∈ gs, Allowed cnotFamily true g) :
    ∃ cs : List (FreeSwaps.Step n), cs.map embedCnot = gs := by
  induction gs with
  | nil => exact ⟨[], rfl⟩
  | cons g gs ih =>
    obtain ⟨cs, rfl⟩ := ih (fun g hg => ha g (List.mem_cons_of_mem _ hg))
    cases g with
    | gate g =>
      obtain ⟨c, rfl⟩ := invertCnot g (ha (.gate g) List.mem_cons_self)
      exact ⟨.gate c :: cs, rfl⟩
    | swap i j => exact ⟨.swap i j :: cs, rfl⟩

private theorem clifford_eq : fullCliffordSynthesis = fullGateFamilySynthesis cnotFamily := by
  ext out
  change Circuit.SynthesizesWithin _ _ ↔ TwoQubit.SynthesizesFrom cnotFamily _ _
  constructor
  · exact TwoQubit.from_circuit _ cnot_supports _ _
  · rintro ⟨gs, ha, hc, hr⟩
    obtain ⟨cs, rfl⟩ := invertCnotList gs ha
    exact ⟨cs, by rwa [TwoQubit.ofGate_cost] at hc, by rwa [TwoQubit.ofGate_run] at hr⟩

private theorem freeSwaps_eq : fullSynthesisWithFreeSwaps = language cnotFamily true := by
  ext out
  change FreeSwaps.Synthesizes _ _ ↔ out ∈ language cnotFamily true
  constructor
  · rintro ⟨cs, hc, hr⟩
    exact ⟨cs.map embedCnot, embedCnot_allowed cs, by rwa [embedCnot_cost], by rwa [embedCnot_run]⟩
  · rintro ⟨gs, ha, hc, hr⟩
    obtain ⟨cs, rfl⟩ := invertCnotFreeSwaps gs ha
    exact ⟨cs, by rwa [embedCnot_cost] at hc, by rwa [embedCnot_run] at hr⟩

private theorem mem_NP (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) (swaps : Bool) :
    language Γ swaps ∈ NP encFullTableauInput := by
  apply mem_NP_of_short Γ swaps (5 * (Polynomial.X + 1) ^ 3)
  intro out hout
  obtain ⟨gs, ha, hc, hr⟩ := hout
  obtain ⟨ss, ha, hc, hr, hl⟩ := bounded_certificate Γ supports swaps _ _ gs ha hc hr
  refine ⟨ss, ha, hc, hr, hl.trans ?_⟩
  have hn : (decodeFull out).qubits ≤ (encFullTableauInput out).length := width_bound out
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  calc
    _ ≤ 5 * ((decodeFull out).qubits + 1) ^ 3 := by nlinarith
    _ ≤ _ := by gcongr

end FullVerifier

theorem fullGateFamily_mem_NP (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    fullGateFamilySynthesis Γ ∈ NP encFullTableauInput := by
  rw [FullVerifier.gateFamily_eq]
  exact FullVerifier.mem_NP Γ supports false

theorem fullGateFamilyFreeSwaps_mem_NP (Γ : Set TwoQubit.Gate) (supports : TwoQubit.SupportsCNOT Γ) :
    fullGateFamilySynthesisWithFreeSwaps Γ ∈ NP encFullTableauInput := by
  rw [FullVerifier.gateFamilyFreeSwaps_eq]
  exact FullVerifier.mem_NP Γ supports true

theorem fullClifford_mem_NP : fullCliffordSynthesis ∈ NP encFullTableauInput := by
  rw [FullVerifier.clifford_eq]
  exact fullGateFamily_mem_NP _ FullVerifier.cnot_supports

theorem fullFreeSwaps_mem_NP : fullSynthesisWithFreeSwaps ∈ NP encFullTableauInput := by
  rw [FullVerifier.freeSwaps_eq]
  exact FullVerifier.mem_NP _ FullVerifier.cnot_supports true

end CliffordFrontier
