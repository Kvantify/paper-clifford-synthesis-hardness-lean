/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.RowRigidity

/-!
# Classical Target

Saturation and allowed row values for any classical implementation of the
concrete replicated target, derived through the actual Clifford semantics.
-/

public section

namespace CliffordSynthesis.ClassicalTarget

open Planes (F)
open RowExtraction (AddGate runRows)
open RowHistory (asCircuit newRow Fresh)
open StandardSpace (standard fieldRows)
open RecorderVectors (embed parity output)
open Target (Wire)

variable {d r n m : Nat}

theorem circuit_final (label : Wire d r ≃ Fin n) (cs : List (AddGate n))
    (t : Fin d → F) (X : Fin r → Fin d → F)
    (hout : ∀ i, runRows cs (standard n).x i = embed label (Target.matrix t X (label.symm i))) :
    ∀ i, (fieldRows (Circuit.run (asCircuit cs) (Circuit.identity n))).x i =
      embed label (Target.matrix t X (label.symm i)) := by
  simpa only [StandardSpace.fieldRows_run, StandardSpace.fieldRows_identity, RowHistory.circuit_x] using hout

theorem fresh (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (cs : List (AddGate n)) (t : Fin d → F)
    (hout : ∀ i, runRows cs (standard n).x i = embed label (Target.matrix t
      (ReplicatedTarget.repeated vertex copies) (label.symm i))) (hbudget : cs.length ≤ r + m) :
    Fresh cs (standard n).x := by
  have hs := ReplicatedTarget.target_saturation label vertex hv hzero copies (asCircuit cs) t
    (circuit_final label cs t _ hout) (by simpa only [RowHistory.circuit_cost] using hbudget)
  exact RowHistory.fresh_of_clifford cs hs.2.2.1

theorem birth_cases (label : Wire d r ≃ Fin n)
    (vertex : Fin (m + 1) → Fin d → F) (hv : Function.Injective vertex) (hzero : vertex 0 = 0)
    (copies : Fin r ≃ Fin (m + 1) × Fin (6 * m + 1)) (cs : List (AddGate n)) (t : Fin d → F)
    (hout : ∀ i, runRows cs (standard n).x i = embed label (Target.matrix t
      (ReplicatedTarget.repeated vertex copies) (label.symm i))) (hbudget : cs.length ≤ r + m)
    (pre post : List (AddGate n)) (g : AddGate n) (heq : cs = pre ++ g :: post) :
    (∃ a, newRow pre g (standard n).x = output label (ReplicatedTarget.repeated vertex copies) a) ∨
      ∃ v : Fin m, newRow pre g (standard n).x = parity label (vertex v.succ) := by
  have hfinal := circuit_final label cs t _ hout
  have hcost : Circuit.cost (asCircuit cs) ≤ r + m := by simpa only [RowHistory.circuit_cost] using hbudget
  have hs := ReplicatedTarget.target_saturation label vertex hv hzero copies (asCircuit cs) t hfinal hcost
  have hp : (pre.length, g.target) ∈ BirthOccurrences.occurrences (StandardSpace.initialW n)
      (asCircuit cs) (standard n) := by simpa only [heq] using RowHistory.birth_at_prefix pre post g
  obtain ⟨j, hj⟩ := Freshness.required_birth_value (StandardSpace.initialW n) (asCircuit cs) (standard n)
    (ReplicatedTarget.required label vertex (ReplicatedTarget.repeated vertex copies))
    (ReplicatedTarget.required_injective label vertex hv _)
    (fun a i => by simpa only [CircuitLedger.initial_visible, ne_eq, Option.some.injEq] using
      ReplicatedTarget.required_not_initial label vertex hv hzero (ReplicatedTarget.repeated vertex copies) a i)
    (ReplicatedTarget.required_visible label vertex copies (asCircuit cs) t hfinal hcost)
    (Nat.le_of_eq hs.2.1) (pre.length, g.target) hp (newRow pre g (standard n).x)
    (by simp only [heq, RowHistory.visible_at, RowHistory.at_after, newRow])
  unfold ReplicatedTarget.required at hj
  cases h : finSumFinEquiv.symm j with
  | inl a => exact Or.inl ⟨a, by simpa only [h, ReplicatedTarget.requiredSum] using hj⟩
  | inr v => exact Or.inr ⟨v, by simpa only [h, ReplicatedTarget.requiredSum] using hj⟩

end CliffordSynthesis.ClassicalTarget
