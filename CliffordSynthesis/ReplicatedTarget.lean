/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.RecorderVectors

/-!
# Replicated Target

The concrete replicated target discharges the vector and counting premises
of the Clifford-to-classical argument. There are m+1 vertices, with start 0.
-/

@[expose] public section

namespace CliffordSynthesis.ReplicatedTarget

open Planes (F)
open StandardSpace (Space standard fieldRows)
open Target (Wire)
open RecorderVectors (embed parity recorder output)
open Observation (visible)

variable {d r n m k : Nat}

def repeated (vertex : Fin (m + 1) → Fin d → F) (copies : Fin r ≃ Fin (m + 1) × Fin k) :
    Fin r → Fin d → F := fun a => vertex (copies a).1

/-- There are at least k concrete recorders for each specified vertex. -/
theorem copies_count (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (copies : Fin r ≃ Fin (m + 1) × Fin k) (v : Fin (m + 1)) :
    k ≤ (Finset.univ.filter (fun a => parity label (repeated vertex copies a) = parity label (vertex v))).card := by
  classical
  let f : Fin k → Fin r := fun b => copies.symm (v, b)
  have hi : Function.Injective f := by
    intro a b hab
    exact Prod.mk.inj (copies.symm.injective hab) |>.2
  have hh := Finset.card_le_card_of_injOn f
    (s := Finset.univ) (t := Finset.univ.filter (fun a => parity label (repeated vertex copies a) = parity label (vertex v)))
    (by
      intro a _
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simp [f, repeated]⟩) hi.injOn
  simpa using hh

/-- Stating the final X rows as rows of the explicit target already implies
the Boolean linear-output condition used by the ledger. -/
theorem target_linear (label : Wire d r ≃ Fin n) (gs : List (Circuit.Gate n))
    (t : Fin d → F) (X : Fin r → Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x i =
      embed label (Target.matrix t X (label.symm i))) :
    ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false := by
  intro i j
  have hh := congrFun (hfinal i) (j, true)
  cases hb : (Circuit.run gs (Circuit.identity n)).x i (j, true)
  · rfl
  · simp [fieldRows, embed, hb, LocalChart.bit] at hh

theorem target_recorder_visible (label : Wire d r ≃ Fin n) (gs : List (Circuit.Gate n))
    (t : Fin d → F) (X : Fin r → Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x i =
      embed label (Target.matrix t X (label.symm i))) :
    ∀ a, visible (StandardSpace.initialW n) (fieldRows (Circuit.run gs (Circuit.identity n)))
      (recorder label a) = some (output label X a) := by
  intro a
  have hx : (fieldRows (Circuit.run gs (Circuit.identity n))).x (recorder label a) = output label X a := by
    simpa only [recorder, Equiv.symm_apply_apply, RecorderVectors.target_recorder_row] using hfinal (recorder label a)
  have hm : (fieldRows (Circuit.run gs (Circuit.identity n))).x (recorder label a) ∈ StandardSpace.initialW n := by
    rw [hx]
    exact RecorderVectors.output_mem label X a
  exact (Observation.x_visible (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _ (StandardSpace.actual_run_symplectic gs) _ hm).trans (congrArg some hx)

/-- Every vertex parity appears in an implementation of the concrete replicated
target with the reduction's budget and replication factor. -/
theorem all_parities_visible (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1))
    (gs : List (Circuit.Gate n)) (t : Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x i =
      embed label (Target.matrix t (repeated vertex copies) (label.symm i)))
    (hbudget : Circuit.cost gs ≤ r + m) (v : Fin (m + 1)) :
    ∃ s ≤ gs.length, ∃ i,
      BirthOccurrences.atTime (StandardSpace.initialW n) gs (standard n) s i = some (parity label (vertex v)) := by
  apply MissingParity.replication_forces_visible (m := m + 1) gs (recorder label)
    (RecorderVectors.recorder_injective label) (output label (repeated vertex copies))
    (fun a => parity label (repeated vertex copies a)) (RecorderVectors.output_injective label _)
    (fun _ => rfl) (RecorderVectors.output_not_initial label _)
    (target_recorder_visible label gs t _ hfinal) (target_linear label gs t _ hfinal)
    (by simpa using hbudget)
  simpa using copies_count label vertex copies v

def requiredSum (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) : Fin r ⊕ Fin m → Space n :=
  fun j => Sum.casesOn j (output label X) (fun v => parity label (vertex v.succ))

def required (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (X : Fin r → Fin d → F) : Fin (r + m) → Space n :=
  fun j => requiredSum label vertex X (finSumFinEquiv.symm j)

theorem requiredSum_injective (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (X : Fin r → Fin d → F) :
    Function.Injective (requiredSum label vertex X) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (RecorderVectors.output_injective label X hab)
    | inr b => exact False.elim (RecorderVectors.parity_ne_output label X (vertex b.succ) a hab.symm)
  | inr a =>
    cases b with
    | inl b => exact False.elim (RecorderVectors.parity_ne_output label X (vertex a.succ) b hab)
    | inr b =>
      exact congrArg Sum.inr (Fin.succ_injective m (hv (RecorderVectors.parity_injective label hab)))

theorem required_injective (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (X : Fin r → Fin d → F) :
    Function.Injective (required label vertex X) :=
  (requiredSum_injective label vertex hv X).comp finSumFinEquiv.symm.injective

theorem required_not_initial (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (X : Fin r → Fin d → F) (j : Fin (r + m)) (i : Fin n) :
    (standard n).x i ≠ required label vertex X j := by
  unfold required
  cases h : finSumFinEquiv.symm j with
  | inl a => exact RecorderVectors.output_not_initial label X a i
  | inr v =>
    apply RecorderVectors.nonzero_parity_not_initial label (vertex v.succ) _ i
    intro hz
    have hh := hv (hz.trans hzero.symm)
    exact Fin.succ_ne_zero v hh

theorem required_visible (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1))
    (gs : List (Circuit.Gate n)) (t : Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x i =
      embed label (Target.matrix t (repeated vertex copies) (label.symm i)))
    (hbudget : Circuit.cost gs ≤ r + m) (j : Fin (r + m)) :
    ∃ s ≤ gs.length, ∃ i, BirthOccurrences.atTime (StandardSpace.initialW n) gs (standard n) s i =
      some (required label vertex (repeated vertex copies) j) := by
  unfold required
  cases h : finSumFinEquiv.symm j with
  | inl a =>
    refine ⟨gs.length, le_rfl, recorder label a, ?_⟩
    have hh := target_recorder_visible label gs t _ hfinal a
    simpa [BirthOccurrences.atTime, StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity, requiredSum] using hh
  | inr v => exact all_parities_visible label vertex copies gs t hfinal hbudget v.succ

/-- The concrete target, source vertices, and budget imply all-T saturation;
the recorder and required-vector hypotheses are discharged internally. -/
theorem target_saturation (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1))
    (gs : List (Circuit.Gate n)) (t : Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x i =
      embed label (Target.matrix t (repeated vertex copies) (label.symm i)))
    (hbudget : Circuit.cost gs ≤ r + m) :
    Circuit.cost gs = r + m ∧
      CircuitLedger.totalBirths (StandardSpace.initialW n) gs (standard n) = r + m ∧
      Saturation.GloballyFresh (StandardSpace.initialW n) gs (standard n) ∧
      ∀ e ∈ CircuitLedger.trace (StandardSpace.initialW n) gs (standard n), e = .T := by
  exact Freshness.actual_required_all_T gs (target_linear label gs t _ hfinal)
    (required label vertex (repeated vertex copies)) (required_injective label vertex hv _)
    (required_not_initial label vertex hv hzero _) (required_visible label vertex copies gs t hfinal hbudget) hbudget

/-- A budget-respecting Clifford implementation of A yields a classical
row-addition implementation of exactly A with r+m additions. -/
theorem target_classical (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1))
    (gs : List (Circuit.Gate n)) (t : Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x i =
      embed label (Target.matrix t (repeated vertex copies) (label.symm i)))
    (hbudget : Circuit.cost gs ≤ r + m) :
    ∃ cs : List (RowExtraction.AddGate n), cs.length = r + m ∧
      ∀ i, RowExtraction.runRows cs (standard n).x i =
        embed label (Target.matrix t (repeated vertex copies) (label.symm i)) := by
  obtain ⟨cs, hlen, hout⟩ := RowExtraction.actual_extract gs (target_linear label gs t _ hfinal)
    (required label vertex (repeated vertex copies)) (required_injective label vertex hv _)
    (required_not_initial label vertex hv hzero _) (required_visible label vertex copies gs t hfinal hbudget) hbudget
  refine ⟨cs, hlen, ?_⟩
  intro i
  have hm : (fieldRows (Circuit.run gs (Circuit.identity n))).x i ∈ StandardSpace.initialW n := by
    rw [hfinal i]
    simp [StandardSpace.initialW_mem, embed]
  have hh := Observation.x_visible (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _ (StandardSpace.actual_run_symplectic gs) i hm
  exact (Option.some.inj ((hout i).symm.trans hh)).trans (hfinal i)

end CliffordSynthesis.ReplicatedTarget
