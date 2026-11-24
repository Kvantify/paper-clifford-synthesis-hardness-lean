/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.HamiltonPath

/-!
# Recording

The recording layer: copy the current path parity into each recorder of
one vertex, with one CNOT per recorder and no change to other rows.
-/

@[expose] public section

namespace CliffordSynthesis.Recording

open Planes (F)
open RowExtraction (AddGate addRow runRows)
open RecorderVectors (recorder)
open PathRows (pathWire)
open Target (Wire)

variable {V : Type*} [AddCommGroup V] {d r n m k : Nat}

def gate (label : Wire d r ≃ Fin n) (a : Fin r) : AddGate n where
  control := pathWire label
  target := recorder label a
  distinct := by simp [pathWire, recorder]

def layer (label : Wire d r ≃ Fin n) (as : List (Fin r)) : List (AddGate n) := as.map (gate label)

theorem untouched (cs : List (AddGate n)) (v : Fin n → V) (i : Fin n)
    (hi : ∀ g ∈ cs, i ≠ g.target) : runRows cs v i = v i := by
  induction cs generalizing v with
  | nil => rfl
  | cons g cs ih =>
    rw [RowHistory.run_cons, ih _ (fun h hh => hi h (List.mem_cons_of_mem _ hh))]
    exact ite_eq_right (hi g List.mem_cons_self)

theorem layer_length (label : Wire d r ≃ Fin n) (as : List (Fin r)) : (layer label as).length = as.length := by
  simp [layer]

theorem layer_path (label : Wire d r ≃ Fin n) (as : List (Fin r)) (v : Fin n → V) :
    runRows (layer label as) v (pathWire label) = v (pathWire label) := by
  apply untouched
  intro g hg
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
  exact (gate label a).distinct

theorem layer_coordinate (label : Wire d r ≃ Fin n) (as : List (Fin r)) (v : Fin n → V) (j : Fin d) :
    runRows (layer label as) v (label (.inl j)) = v (label (.inl j)) := by
  apply untouched
  intro g hg
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
  simp [gate, recorder]

theorem layer_recorder (label : Wire d r ≃ Fin n) (as : List (Fin r)) (hn : as.Nodup)
    (v : Fin n → V) (a : Fin r) :
    runRows (layer label as) v (recorder label a) =
      v (recorder label a) + if a ∈ as then v (pathWire label) else 0 := by
  induction as generalizing v with
  | nil => simp [layer, RowHistory.run_nil]
  | cons b bs ih =>
    have hn' := List.nodup_cons.mp hn
    change runRows (layer label bs) (addRow (gate label b) v) (recorder label a) = _
    rw [ih hn'.2]
    have hpath : addRow (gate label b) v (pathWire label) = v (pathWire label) := by
      simp [addRow, gate, pathWire, recorder]
    rw [hpath]
    by_cases hab : a = b
    · subst b
      simp [addRow, gate, hn'.1]
    · have hr : recorder label a ≠ recorder label b := (RecorderVectors.recorder_injective label).ne hab
      simp [addRow, gate, hr, hab]

def indices (copies : Fin r ≃ Fin (m + 1) × Fin k) (u : Fin (m + 1)) : List (Fin r) :=
  List.ofFn (fun b : Fin k => copies.symm (u, b))

theorem indices_length (copies : Fin r ≃ Fin (m + 1) × Fin k) (u : Fin (m + 1)) :
    (indices copies u).length = k := by simp [indices]

theorem indices_nodup (copies : Fin r ≃ Fin (m + 1) × Fin k) (u : Fin (m + 1)) :
    (indices copies u).Nodup := by
  apply List.nodup_ofFn.mpr
  intro a b hab
  exact Prod.mk.inj (copies.symm.injective hab) |>.2

theorem mem_indices (copies : Fin r ≃ Fin (m + 1) × Fin k) (u : Fin (m + 1)) (a : Fin r) :
    a ∈ indices copies u ↔ (copies a).1 = u := by
  simp only [indices, List.mem_ofFn]
  constructor
  · rintro ⟨b, hb⟩
    have hh := congrArg copies hb
    simpa using congrArg Prod.fst hh.symm
  · intro ha
    refine ⟨(copies a).2, ?_⟩
    apply copies.injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext <;> simp_all

end CliffordSynthesis.Recording
