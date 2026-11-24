/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Observation
public import CliffordSynthesis.Ledger

/-!
# Circuit Ledger

The amortized ledger derived from a Clifford circuit, rather than assumed
as a separate valid event trace. H and S contribute no events.
-/

@[expose] public section

namespace CliffordSynthesis.CircuitLedger

open LinearMap (BilinForm)
open Planes (F)
open SymplecticCircuit (Rows IsSymplectic applyGate run)
open Observation (visible present count signature)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

def classify : Nat × Nat × Nat → Ledger.Event
  | (2, 2, 1) => .T
  | (2, 0, 0) => .D
  | (0, 2, 2) => .U
  | (0, 1, 1) => .P
  | (1, 0, 0) => .M
  | (2, 2, 0) => .Z₂
  | (1, 1, 0) => .Z₁
  | _ => .Z₀

theorem classify_spec (s : Nat × Nat × Nat) (hs : Local.permitted s = true) :
    (classify s).before = s.1 ∧ (classify s).after = s.2.1 ∧
    (classify s).births = s.2.2 := by
  simp only [Local.permitted, List.contains_iff_mem, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

noncomputable def trace (W : Submodule F V) : List (Circuit.Gate n) → Rows n V → List Ledger.Event
  | [], _ => []
  | .H q :: gs, a => trace W gs (applyGate (.H q) a)
  | .S q :: gs, a => trace W gs (applyGate (.S q) a)
  | .CX c t hct :: gs, a =>
    classify (signature W a (applyGate (.CX c t hct) a) c t) ::
      trace W gs (applyGate (.CX c t hct) a)

theorem trace_length (W : Submodule F V) (gs : List (Circuit.Gate n)) (a : Rows n V) :
    (trace W gs a).length = Circuit.cost gs := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => cases g <;> simp [trace, Circuit.cost, Circuit.paid, ih, Nat.add_comm]

/-- The actual visible-wire counts obey the event ledger at every step. -/
theorem trace_run (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a) :
    Ledger.Run (count W a) (count W (run gs a)) (trace W gs a) := by
  induction gs generalizing a with
  | nil => exact Ledger.Run.nil _
  | cons g gs ih =>
    have ht := ih (applyGate g a) (SymplecticCircuit.gate_symplectic B a ha g)
    cases g with
    | H q =>
      have hc : count W (applyGate (.H q) a) = count W a := by
        simp [count, applyGate, Observation.hadamard_visible B W hW a ha]
      simpa only [trace, run, hc] using ht
    | S q =>
      have hc : count W (applyGate (.S q) a) = count W a := by
        simp [count, applyGate, Observation.phase_visible B W hW a ha]
      simpa only [trace, run, hc] using ht
    | CX c t hct =>
      have hs := classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
      obtain ⟨untouched, hbefore, hafter⟩ := Observation.cnot_counts W a c t hct
      change Ledger.Run (count W a) _ (_ :: _)
      rw [hbefore, ← hs.1]
      apply Ledger.Run.cons
      simpa only [applyGate, run, hafter, ← hs.2.1] using ht

/-- The appearance ledger for circuits whose initial and final represented-qubit counts agree. -/
theorem amortized (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a)
    (hc : count W (run gs a) = count W a) :
    Ledger.births (trace W gs a) ≤ Circuit.cost gs ∧
    2 * (Circuit.cost gs - Ledger.births (trace W gs a)) = Ledger.penalty (trace W gs a) ∧
    Ledger.exceptional (trace W gs a) ≤
      2 * (Circuit.cost gs - Ledger.births (trace W gs a)) := by
  have hr := trace_run B W hW gs a ha
  rw [hc] at hr
  simpa only [trace_length] using Ledger.amortized hr

theorem initial_visible (n : Nat) (i : Fin n) :
    visible (StandardSpace.initialW n) (StandardSpace.standard n) i =
      some ((StandardSpace.standard n).x i) := by
  apply (Observation.observe_eq_some (StandardSpace.form n) _
    (StandardSpace.initialW_isotropic n) _ _
    (by constructor <;> simp [(StandardSpace.standard_symplectic n).xx,
      (StandardSpace.standard_symplectic n).xz, (StandardSpace.standard_symplectic n).zx,
      (StandardSpace.standard_symplectic n).zz]) _).mpr
  refine ⟨?_, ?_, Submodule.subset_span (by simp)⟩
  · intro hz
    have hi := congrFun hz (i, false)
    simp [StandardSpace.standard] at hi
  · simp [StandardSpace.initialW_mem, StandardSpace.standard]

theorem initial_count (n : Nat) :
    count (StandardSpace.initialW n) (StandardSpace.standard n) = n := by
  simp [count, initial_visible, present]

/-- The Boolean circuit semantics induces a valid ledger starting with n visible wires. -/
theorem actual_trace_run (gs : List (Circuit.Gate n)) :
    Ledger.Run n
      (count (StandardSpace.initialW n)
        (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))))
      (trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  have hr := trace_run (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) gs _ (StandardSpace.standard_symplectic n)
  simpa only [initial_count, StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity] using hr

/-- The actual circuit's amortized birth bound, under its endpoint representation
condition. No abstract trace-validity assumption is needed. -/
theorem actual_amortized (gs : List (Circuit.Gate n))
    (hfinal : count (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) = n) :
    let es := trace (StandardSpace.initialW n) gs (StandardSpace.standard n)
    Ledger.births es ≤ Circuit.cost gs ∧
    2 * (Circuit.cost gs - Ledger.births es) = Ledger.penalty es ∧
    Ledger.exceptional es ≤ 2 * (Circuit.cost gs - Ledger.births es) := by
  have hr := actual_trace_run gs
  rw [hfinal] at hr
  simpa only [trace_length] using Ledger.amortized hr

/-- Count each wire's changes to a nonempty visible vector, including all gate
boundaries; this definition does not use the event classification. -/
noncomputable def totalBirths (W : Submodule F V) (gs : List (Circuit.Gate n)) : Rows n V → Nat :=
  gs.rec (fun _ => 0) (fun g _ tail a =>
    Observation.stepBirths W a (applyGate g a) + tail (applyGate g a))

theorem trace_births (B : BilinForm F V) (W : Submodule F V) (hW : Splitting.Isotropic B W)
    (gs : List (Circuit.Gate n)) (a : Rows n V) (ha : IsSymplectic B a) :
    Ledger.births (trace W gs a) = totalBirths W gs a := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    have hi := ih (applyGate g a) (SymplecticCircuit.gate_symplectic B a ha g)
    cases g with
    | H q =>
      simpa only [trace, totalBirths, applyGate,
        Observation.hadamard_births B W hW a ha, zero_add] using hi
    | S q =>
      simpa only [trace, totalBirths, applyGate,
        Observation.phase_births B W hW a ha, zero_add] using hi
    | CX c t hct =>
      have hs := classify_spec _ (Observation.cnot_localTable B W hW a ha c t hct)
      simp only [trace, totalBirths, Ledger.births, applyGate,
        Observation.cnot_births W a c t hct, hs.2.2]
      exact congrArg (_ + ·) hi

/-- A numerical statement about births of actual ambient vectors on physical
wires. The trace is constructed internally and only used to count exceptions. -/
theorem actual_birth_bound (gs : List (Circuit.Gate n))
    (hfinal : count (StandardSpace.initialW n)
      (StandardSpace.fieldRows (Circuit.run gs (Circuit.identity n))) = n) :
    totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n) ≤ Circuit.cost gs ∧
    Ledger.exceptional (trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) ≤
      2 * (Circuit.cost gs - totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  have hb := actual_amortized gs hfinal
  have he := trace_births (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) gs _ (StandardSpace.standard_symplectic n)
  dsimp only at hb
  rw [he] at hb
  exact ⟨hb.1, hb.2.2⟩

/-- In particular, the bound applies whenever the output X rows involve only
input X coordinates, as for the linear target. -/
theorem actual_linear_birth_bound (gs : List (Circuit.Gate n))
    (hlinear : ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false) :
    totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n) ≤ Circuit.cost gs ∧
    Ledger.exceptional (trace (StandardSpace.initialW n) gs (StandardSpace.standard n)) ≤
      2 * (Circuit.cost gs - totalBirths (StandardSpace.initialW n) gs (StandardSpace.standard n)) := by
  apply actual_birth_bound gs
  apply Observation.count_of_all_x (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _ (StandardSpace.actual_run_symplectic gs)
  intro i
  simp [StandardSpace.initialW_mem, StandardSpace.fieldRows, hlinear, LocalChart.bit]

end CliffordSynthesis.CircuitLedger
