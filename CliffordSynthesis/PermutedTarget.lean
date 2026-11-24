/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.DisplacedRecorders
public import CliffordSynthesis.ClassicalTarget

/-!
# Permuted Target

Saturation and classical extraction for the replicated target with an
arbitrary final permutation of its physical wires.
-/

public section

namespace CliffordSynthesis.PermutedTarget

open Planes (F)
open StandardSpace (Space standard fieldRows)
open Target (Wire)
open RecorderVectors (embed parity recorder output)
open Observation (visible)
open ReplicatedTarget (repeated copies_count required requiredSum required_injective required_not_initial)

variable {d r n m : Nat}

theorem target_linear (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n)) (gs : List (Circuit.Gate n))
    (t : Fin d → F) (X : Fin r → Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x (perm i) =
      embed label (Target.matrix t X (label.symm i))) :
    ∀ i j, (Circuit.run gs (Circuit.identity n)).x i (j, true) = false := by
  intro i j
  have hh := congrFun (hfinal (perm.symm i)) (j, true)
  simp only [Equiv.apply_symm_apply] at hh
  cases hb : (Circuit.run gs (Circuit.identity n)).x i (j, true)
  · rfl
  · simp [fieldRows, embed, hb, LocalChart.bit] at hh

theorem target_recorder_visible (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n)) (gs : List (Circuit.Gate n))
    (t : Fin d → F) (X : Fin r → Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x (perm i) =
      embed label (Target.matrix t X (label.symm i))) :
    ∀ a, visible (StandardSpace.initialW n) (fieldRows (Circuit.run gs (Circuit.identity n)))
      (perm (recorder label a)) = some (output label X a) := by
  intro a
  have hx : (fieldRows (Circuit.run gs (Circuit.identity n))).x (perm (recorder label a)) = output label X a := by
    simpa only [recorder, Equiv.symm_apply_apply, RecorderVectors.target_recorder_row] using hfinal (recorder label a)
  have hm : (fieldRows (Circuit.run gs (Circuit.identity n))).x (perm (recorder label a)) ∈ StandardSpace.initialW n := by
    rw [hx]
    exact RecorderVectors.output_mem label X a
  exact (Observation.x_visible (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _ (StandardSpace.actual_run_symplectic gs) _ hm).trans (congrArg some hx)

/-- Every vertex parity appears in an implementation of the concrete replicated
target with the reduction's budget and replication factor. -/
theorem all_parities_visible (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n)) (vertex : Fin (m + 1) → Fin d → F)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1))
    (gs : List (Circuit.Gate n)) (t : Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x (perm i) =
      embed label (Target.matrix t (repeated vertex copies) (label.symm i)))
    (hbudget : Circuit.cost gs ≤ r + m) (v : Fin (m + 1)) :
    ∃ s ≤ gs.length, ∃ i,
      BirthOccurrences.atTime (StandardSpace.initialW n) gs (standard n) s i = some (parity label (vertex v)) := by
  by_contra h
  push Not at h
  have hh := DisplacedRecorders.missing_cost_bound label (repeated vertex copies) gs
    (fun a => perm (recorder label a)) (perm.injective.comp (RecorderVectors.recorder_injective label))
    (target_recorder_visible label perm gs t _ hfinal) (target_linear label perm gs t _ hfinal)
    (parity label (vertex v)) h
  have hc := copies_count label vertex copies v
  omega

theorem required_visible (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n)) (vertex : Fin (m + 1) → Fin d → F)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1))
    (gs : List (Circuit.Gate n)) (t : Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x (perm i) =
      embed label (Target.matrix t (repeated vertex copies) (label.symm i)))
    (hbudget : Circuit.cost gs ≤ r + m) (j : Fin (r + m)) :
    ∃ s ≤ gs.length, ∃ i, BirthOccurrences.atTime (StandardSpace.initialW n) gs (standard n) s i =
      some (required label vertex (repeated vertex copies) j) := by
  unfold required
  cases h : finSumFinEquiv.symm j with
  | inl a =>
    refine ⟨gs.length, le_rfl, perm (recorder label a), ?_⟩
    have hh := target_recorder_visible label perm gs t _ hfinal a
    simpa [BirthOccurrences.atTime, StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity, requiredSum] using hh
  | inr v => exact all_parities_visible label perm vertex copies gs t hfinal hbudget v.succ

/-- The concrete target, source vertices, and budget imply all-T saturation;
the recorder and required-vector hypotheses are discharged internally. -/
theorem target_saturation (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n))
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1))
    (gs : List (Circuit.Gate n)) (t : Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x (perm i) =
      embed label (Target.matrix t (repeated vertex copies) (label.symm i)))
    (hbudget : Circuit.cost gs ≤ r + m) :
    Circuit.cost gs = r + m ∧
      CircuitLedger.totalBirths (StandardSpace.initialW n) gs (standard n) = r + m ∧
      Saturation.GloballyFresh (StandardSpace.initialW n) gs (standard n) ∧
      ∀ e ∈ CircuitLedger.trace (StandardSpace.initialW n) gs (standard n), e = .T := by
  exact Freshness.actual_required_all_T gs (target_linear label perm gs t _ hfinal)
    (required label vertex (repeated vertex copies)) (required_injective label vertex hv _)
    (required_not_initial label vertex hv hzero _) (required_visible label perm vertex copies gs t hfinal hbudget) hbudget

/-- A budget-respecting Clifford implementation of A yields a classical
row-addition implementation of exactly A with r+m additions. -/
theorem target_classical (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n))
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1))
    (gs : List (Circuit.Gate n)) (t : Fin d → F)
    (hfinal : ∀ i, (fieldRows (Circuit.run gs (Circuit.identity n))).x (perm i) =
      embed label (Target.matrix t (repeated vertex copies) (label.symm i)))
    (hbudget : Circuit.cost gs ≤ r + m) :
    ∃ cs : List (RowExtraction.AddGate n), cs.length = r + m ∧
      ∀ i, RowExtraction.runRows cs (standard n).x (perm i) =
        embed label (Target.matrix t (repeated vertex copies) (label.symm i)) := by
  obtain ⟨cs, hlen, hout⟩ := RowExtraction.actual_extract gs (target_linear label perm gs t _ hfinal)
    (required label vertex (repeated vertex copies)) (required_injective label vertex hv _)
    (required_not_initial label vertex hv hzero _) (required_visible label perm vertex copies gs t hfinal hbudget) hbudget
  refine ⟨cs, hlen, ?_⟩
  intro i
  have hm : (fieldRows (Circuit.run gs (Circuit.identity n))).x (perm i) ∈ StandardSpace.initialW n := by
    rw [hfinal i]
    simp [StandardSpace.initialW_mem, embed]
  have hh := Observation.x_visible (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _ (StandardSpace.actual_run_symplectic gs) (perm i) hm
  exact (Option.some.inj ((hout (perm i)).symm.trans hh)).trans (hfinal i)

open RowExtraction (AddGate runRows)
open RowHistory (asCircuit newRow Fresh)

theorem circuit_final (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n)) (cs : List (AddGate n))
    (t : Fin d → F) (X : Fin r → Fin d → F)
    (hout : ∀ i, runRows cs (standard n).x (perm i) = embed label (Target.matrix t X (label.symm i))) :
    ∀ i, (fieldRows (Circuit.run (asCircuit cs) (Circuit.identity n))).x (perm i) =
      embed label (Target.matrix t X (label.symm i)) := by
  simpa only [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity, RowHistory.circuit_x] using hout

theorem fresh (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n))
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (cs : List (AddGate n)) (t : Fin d → F)
    (hout : ∀ i, runRows cs (standard n).x (perm i) = embed label (Target.matrix t
      (ReplicatedTarget.repeated vertex copies) (label.symm i))) (hbudget : cs.length ≤ r + m) :
    Fresh cs (standard n).x := by
  have hs := target_saturation label perm vertex hv hzero copies (asCircuit cs) t
    (circuit_final label perm cs t _ hout) (by simpa only [RowHistory.circuit_cost] using hbudget)
  exact RowHistory.fresh_of_clifford cs hs.2.2.1

theorem birth_cases (label : Wire d r ≃ Fin n) (perm : Equiv.Perm (Fin n))
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (cs : List (AddGate n)) (t : Fin d → F)
    (hout : ∀ i, runRows cs (standard n).x (perm i) = embed label (Target.matrix t
      (ReplicatedTarget.repeated vertex copies) (label.symm i))) (hbudget : cs.length ≤ r + m)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post) :
    (∃ a, newRow pre g (standard n).x = output label (ReplicatedTarget.repeated vertex copies) a) ∨
      ∃ v : Fin m, newRow pre g (standard n).x = parity label (vertex v.succ) := by
  have hfinal := circuit_final label perm cs t _ hout
  have hcost : Circuit.cost (asCircuit cs) ≤ r + m := by simpa only [RowHistory.circuit_cost] using hbudget
  have hs := target_saturation label perm vertex hv hzero copies (asCircuit cs) t hfinal hcost
  have hp : (pre.length, g.target) ∈ BirthOccurrences.occurrences (StandardSpace.initialW n)
      (asCircuit cs) (standard n) := by simpa only [heq] using RowHistory.birth_at_prefix pre post g
  obtain ⟨j, hj⟩ := Freshness.required_birth_value (StandardSpace.initialW n) (asCircuit cs) (standard n)
    (ReplicatedTarget.required label vertex (ReplicatedTarget.repeated vertex copies))
    (ReplicatedTarget.required_injective label vertex hv _)
    (fun a i => by simpa only [CircuitLedger.initial_visible, ne_eq, Option.some.injEq] using
      ReplicatedTarget.required_not_initial label vertex hv hzero (ReplicatedTarget.repeated vertex copies) a i)
    (required_visible label perm vertex copies (asCircuit cs) t hfinal hcost)
    (Nat.le_of_eq hs.2.1) (pre.length, g.target) hp (newRow pre g (standard n).x)
    (by simp only [heq, RowHistory.visible_at, RowHistory.at_after, newRow])
  unfold ReplicatedTarget.required at hj
  cases h : finSumFinEquiv.symm j with
  | inl a => exact Or.inl ⟨a, by simpa only [h, ReplicatedTarget.requiredSum] using hj⟩
  | inr v => exact Or.inr ⟨v, by simpa only [h, ReplicatedTarget.requiredSum] using hj⟩

end CliffordSynthesis.PermutedTarget
