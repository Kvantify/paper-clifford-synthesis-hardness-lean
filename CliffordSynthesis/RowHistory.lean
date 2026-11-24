/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.EncodedTarget

/-!
# Row History

Classical row histories as actual CNOT-only Clifford histories. This allows
the proved saturation theorem to be applied to any extracted row circuit.
-/

@[expose] public section

namespace CliffordSynthesis.RowHistory

open Planes (F)
open RowExtraction (AddGate addRow runRows)
open StandardSpace (Space standard)

variable {V : Type*} [AddCommGroup V] [Module F V] {n : Nat}

def asGate (g : AddGate n) : Circuit.Gate n := .CX g.control g.target g.distinct
def asCircuit (cs : List (AddGate n)) : List (Circuit.Gate n) := cs.map asGate

def rowAt (cs : List (AddGate n)) (v : Fin n → V) (k : Nat) : Fin n → V := runRows (cs.take k) v

def newRow (pre : List (AddGate n)) (g : AddGate n) (v : Fin n → V) : V :=
  addRow g (runRows pre v) g.target

def Fresh (cs : List (AddGate n)) (v : Fin n → V) : Prop :=
  ∀ pre g post, cs = pre ++ g :: post → ∀ s ≤ pre.length, ∀ i, newRow pre g v ≠ rowAt cs v s i

omit [Module F V] in
theorem run_nil (v : Fin n → V) : runRows [] v = v := rfl

omit [Module F V] in
theorem run_cons (g : AddGate n) (cs : List (AddGate n)) (v : Fin n → V) :
    runRows (g :: cs) v = runRows cs (addRow g v) := rfl

omit [Module F V] in
theorem run_singleton (g : AddGate n) (v : Fin n → V) : runRows [g] v = addRow g v := rfl

omit [Module F V] in
theorem newRow_eq (pre : List (AddGate n)) (g : AddGate n) (v : Fin n → V) :
    newRow pre g v = runRows pre v g.target + runRows pre v g.control := by simp [newRow, addRow]

omit [Module F V] in
theorem run_append (cs ds : List (AddGate n)) (v : Fin n → V) :
    runRows (cs ++ ds) v = runRows ds (runRows cs v) := by
  induction cs generalizing v with
  | nil => rfl
  | cons g cs ih => exact ih (addRow g v)

omit [Module F V] in
theorem at_prefix (pre post : List (AddGate n)) (v : Fin n → V) :
    rowAt (pre ++ post) v pre.length = runRows pre v := by simp [rowAt]

omit [Module F V] in
theorem at_after (pre post : List (AddGate n)) (g : AddGate n) (v : Fin n → V) :
    rowAt (pre ++ g :: post) v (pre.length + 1) = addRow g (runRows pre v) := by
  have ht : (pre ++ g :: post).take (pre.length + 1) = pre ++ [g] := by
    simp [List.take_append, List.take_of_length_le (Nat.le_succ pre.length)]
  rw [rowAt, ht, run_append]
  rfl

theorem circuit_cost (cs : List (AddGate n)) : Circuit.cost (asCircuit cs) = cs.length := by
  induction cs with
  | nil => rfl
  | cons g cs ih =>
    change 1 + Circuit.cost (asCircuit cs) = cs.length + 1
    omega

omit [Module F V] in
theorem circuit_x (cs : List (AddGate n)) (a : SymplecticCircuit.Rows n V) :
    (SymplecticCircuit.run (asCircuit cs) a).x = runRows cs a.x := by
  induction cs generalizing a with
  | nil => rfl
  | cons g cs ih =>
    change (SymplecticCircuit.run (asCircuit cs) (SymplecticCircuit.CX g.control g.target a)).x =
      runRows cs (addRow g a.x)
    rw [ih]
    rfl

theorem rows_mem (W : Submodule F V) (cs : List (AddGate n)) (v : Fin n → V)
    (hv : ∀ i, v i ∈ W) : ∀ i, runRows cs v i ∈ W := by
  induction cs generalizing v with
  | nil => exact hv
  | cons g cs ih =>
    apply ih
    intro i
    dsimp [addRow]
    split_ifs
    · exact W.add_mem (hv i) (hv g.control)
    · exact hv i

theorem actual_visible (cs : List (AddGate n)) (i : Fin n) :
    Observation.visible (StandardSpace.initialW n)
      (SymplecticCircuit.run (asCircuit cs) (standard n)) i = some (runRows cs (standard n).x i) := by
  have hm : ∀ i, runRows cs (standard n).x i ∈ StandardSpace.initialW n :=
    rows_mem _ cs _ (fun i => by simp [StandardSpace.initialW_mem, standard])
  have hs := SymplecticCircuit.run_symplectic (StandardSpace.form n) (asCircuit cs) _ (StandardSpace.standard_symplectic n)
  have hh := Observation.x_visible (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _ hs i (by simpa only [circuit_x] using hm i)
  simpa only [circuit_x] using hh

theorem visible_at (cs : List (AddGate n)) (k : Nat) (i : Fin n) :
    BirthOccurrences.atTime (StandardSpace.initialW n) (asCircuit cs) (standard n) k i =
      some (rowAt cs (standard n).x k i) := by
  simpa only [BirthOccurrences.atTime, rowAt, asCircuit, List.map_take] using actual_visible (cs.take k) i

theorem rows_injective (cs : List (AddGate n)) : Function.Injective (runRows cs (standard n).x) := by
  intro i j hij
  by_contra h
  exact WireGeometry.visible_distinct (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _
    (SymplecticCircuit.run_symplectic _ _ _ (StandardSpace.standard_symplectic n))
    i j h _ _ (actual_visible cs i) (actual_visible cs j) hij

theorem row_ne_zero (cs : List (AddGate n)) (i : Fin n) : runRows cs (standard n).x i ≠ 0 := by
  have hh := (WireGeometry.visible_spec (StandardSpace.form n) (StandardSpace.initialW n)
    (StandardSpace.initialW_isotropic n) _
    (SymplecticCircuit.run_symplectic _ _ _ (StandardSpace.standard_symplectic n)) i _).mp (actual_visible cs i)
  exact hh.1

theorem target_changes (pre : List (AddGate n)) (g : AddGate n) :
    newRow pre g (standard n).x ≠ runRows pre (standard n).x g.target := by
  simpa [newRow, addRow] using row_ne_zero pre g.control

theorem birth_at_prefix (pre post : List (AddGate n)) (g : AddGate n) :
    (pre.length, g.target) ∈ BirthOccurrences.occurrences (StandardSpace.initialW n)
      (asCircuit (pre ++ g :: post)) (standard n) := by
  rw [BirthOccurrences.occurrence_iff]
  refine ⟨?_, ?_, ?_⟩
  · simp [asCircuit]
  · simp [visible_at]
  · simp only [visible_at, at_after, at_prefix, ne_eq, Option.some.injEq]
    exact target_changes pre g

theorem fresh_of_clifford (cs : List (AddGate n))
    (hf : Saturation.GloballyFresh (StandardSpace.initialW n) (asCircuit cs) (standard n)) :
    Fresh cs (standard n).x := by
  intro pre g post heq s hs i he
  subst cs
  have hb := birth_at_prefix pre post g
  apply hf _ _ (newRow pre g (standard n).x) hb
    (by simp only [visible_at, at_after, newRow]) s hs i
  simp only [visible_at, he]

end CliffordSynthesis.RowHistory
