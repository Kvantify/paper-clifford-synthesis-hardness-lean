/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.Recording

/-!
# Walk Construction

Constructing the classical row circuit by recording each visited vertex and
moving the path parity by one coordinate CNOT along each cube edge.
-/

@[expose] public section

namespace CliffordSynthesis.WalkConstruction

open Planes (F)
open RowExtraction (AddGate addRow runRows)
open StandardSpace (Space standard)
open RecorderVectors (parity recorder output embed)
open PathRows (pathWire)
open Target (Wire)

variable {d r n m k : Nat}

theorem edge_coordinate (label : Wire d r ≃ Fin n) (u v : Fin d → F) (he : hammingDist u v = 1) :
    ∃ j : Fin d, parity label v = parity label u + (standard n).x (label (.inl j)) := by
  classical
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp he
  have hne : u j ≠ v j := by
    have hh : j ∈ Finset.univ.filter (fun i => u i ≠ v i) := by rw [hj]; simp
    simpa using hh
  have hk : ∀ i, v i = u i + if i = j then 1 else 0 := by
    intro i
    by_cases hi : i = j
    · subst i
      have htwo : ∀ a b : F, a ≠ b → b = a + 1 := by decide
      simpa using htwo _ _ hne
    · have hh : u i = v i := by
        by_contra h
        have hm : i ∈ Finset.univ.filter (fun i => u i ≠ v i) := by simp [h]
        rw [hj] at hm
        exact hi (Finset.mem_singleton.mp hm)
      simp [hi, hh]
  refine ⟨j, ?_⟩
  funext p
  rcases p with ⟨i, b⟩
  obtain ⟨w, rfl⟩ := label.surjective i
  cases b
  · rcases w with i | (i | i) <;>
      simp [parity, RecorderVectors.embed_apply, RecorderVectors.rawParity,
        Pi.add_apply, RecorderVectors.basis_apply, hk]
  · simp [parity, embed, standard]

def move (label : Wire d r ≃ Fin n) (j : Fin d) : AddGate n where
  control := label (.inl j)
  target := pathWire label
  distinct := by simp [pathWire]

theorem move_coordinate (label : Wire d r ≃ Fin n) (j i : Fin d) (rows : Fin n → Space n) :
    addRow (move label j) rows (label (.inl i)) = rows (label (.inl i)) := by
  simp [addRow, move, pathWire]

theorem move_recorder (label : Wire d r ≃ Fin n) (j : Fin d) (a : Fin r) (rows : Fin n → Space n) :
    addRow (move label j) rows (recorder label a) = rows (recorder label a) := by
  simp [addRow, move, pathWire, recorder]

theorem move_path (label : Wire d r ≃ Fin n) (j : Fin d) (rows : Fin n → Space n) :
    addRow (move label j) rows (pathWire label) = rows (pathWire label) + rows (label (.inl j)) := by
  simp [addRow, move]

/-- A simple cube walk can be implemented from arbitrary recorder contents.
Exactly the recorders owned by vertices in its support receive their parity. -/
theorem walk_rows (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (copies : Fin r ≃ Fin (m + 1) × Fin k) {u w : Fin (m + 1)}
    (p : (HamiltonPath.cubeGraph vertex).Walk u w) (hp : p.IsPath)
    (rows : Fin n → Space n)
    (hc : ∀ j, rows (label (.inl j)) = (standard n).x (label (.inl j)))
    (hu : rows (pathWire label) = parity label (vertex u)) :
    ∃ cs : List (AddGate n), cs.length = p.length + k * p.support.length ∧
      (∀ j, runRows cs rows (label (.inl j)) = (standard n).x (label (.inl j))) ∧
      runRows cs rows (pathWire label) = parity label (vertex w) ∧
      ∀ a, runRows cs rows (recorder label a) = rows (recorder label a) +
        if (copies a).1 ∈ p.support then parity label (vertex (copies a).1) else 0 := by
  induction p generalizing rows with
  | @nil u =>
    refine ⟨Recording.layer label (Recording.indices copies u), ?_, ?_, ?_, ?_⟩
    · simp [Recording.layer_length, Recording.indices_length]
    · intro j
      rw [Recording.layer_coordinate, hc j]
    · exact (Recording.layer_path label _ rows).trans hu
    · intro a
      rw [Recording.layer_recorder label _ (Recording.indices_nodup copies u), hu]
      by_cases ha : (copies a).1 = u <;> simp [Recording.mem_indices, ha]
  | @cons u v w he p ih =>
    have hpath := (SimpleGraph.Walk.cons_isPath_iff he p).mp hp
    obtain ⟨j, hj⟩ := edge_coordinate label (vertex u) (vertex v) he
    let rs := Recording.layer label (Recording.indices copies u)
    let next := addRow (move label j) (runRows rs rows)
    have hnc : ∀ i, next (label (.inl i)) = (standard n).x (label (.inl i)) := by
      intro i
      dsimp only [next, rs]
      rw [move_coordinate, Recording.layer_coordinate, hc i]
    have hnp : next (pathWire label) = parity label (vertex v) := by
      dsimp only [next, rs]
      rw [move_path, Recording.layer_path, Recording.layer_coordinate, hu, hc j]
      exact hj.symm
    have hnr : ∀ a, next (recorder label a) = rows (recorder label a) +
        if (copies a).1 = u then parity label (vertex (copies a).1) else 0 := by
      intro a
      dsimp only [next, rs]
      rw [move_recorder, Recording.layer_recorder label _ (Recording.indices_nodup copies u), hu]
      by_cases ha : (copies a).1 = u <;> simp [Recording.mem_indices, ha]
    obtain ⟨cs, hlen, hcc, hcp, hcr⟩ := ih hpath.1 next hnc hnp
    refine ⟨rs ++ move label j :: cs, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, hlen, rs, Recording.layer_length,
        Recording.indices_length, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.support_cons, List.length_cons]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · intro i
      simpa only [RowHistory.run_append, RowHistory.run_cons, next] using hcc i
    · simpa only [RowHistory.run_append, RowHistory.run_cons, next] using hcp
    · intro a
      rw [RowHistory.run_append, RowHistory.run_cons]
      change runRows cs next (recorder label a) = _
      rw [hcr a, hnr a]
      by_cases ha : (copies a).1 = u
      · simp [ha, hpath.2]
      · simp [ha]

end CliffordSynthesis.WalkConstruction
