/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.WalkConstruction
public import CliffordSynthesis.ClassicalLift

/-!
# Reduction

Both directions of the concrete induced-cube Hamiltonian-path reduction.
Polynomial-time encoding bounds and the complexity-theory assembly are separate.
-/

@[expose] public section

namespace CliffordSynthesis.Reduction

open Planes (F)
open RowExtraction (AddGate runRows)
open StandardSpace (standard)
open RecorderVectors (embed)
open Target (Wire)

variable {d r n m k : Nat}

/-- A Hamiltonian path implements all rows of A with R+m CNOT row additions,
where there are m+1 vertices and R recorders. -/
theorem hamiltonian_rows (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (hzero : vertex 0 = 0) (copies : Fin r ≃ Fin (m + 1) × Fin k) (last : Fin (m + 1))
    (p : (HamiltonPath.cubeGraph vertex).Walk 0 last) (hp : p.IsHamiltonian) :
    ∃ cs : List (AddGate n), cs.length = r + m ∧
      ∀ i, runRows cs (standard n).x i = embed label (Target.matrix (vertex last)
        (ReplicatedTarget.repeated vertex copies) (label.symm i)) := by
  obtain ⟨cs, hlen, hc, hpath, hr⟩ := WalkConstruction.walk_rows label vertex copies p hp.isPath
    (standard n).x (fun _ => rfl)
    (by simp only [hzero, RecorderVectors.zero_parity, PathRows.pathWire])
  have hR : r = (m + 1) * k := by simpa using Fintype.card_congr copies
  have hlength : cs.length = r + m := by
    rw [hp.length_eq, hp.length_support] at hlen
    simpa [hR, Nat.mul_comm, Nat.add_comm] using hlen
  refine ⟨cs, hlength, ?_⟩
  intro i
  obtain ⟨w, rfl⟩ := label.surjective i
  simp only [Equiv.symm_apply_apply]
  rcases w with j | (u | a)
  · rw [RecorderVectors.target_coordinate_row]
    exact hc j
  · cases u
    rw [RecorderVectors.target_path_row]
    exact hpath
  · rw [RecorderVectors.target_recorder_row]
    have hh := hr a
    rw [ite_eq_left (hp.mem_support (copies a).1)] at hh
    exact hh

/-- The complete Boolean tableau, including its inverse-transpose Z block,
has a CNOT-only implementation of the prescribed cost. -/
theorem hamiltonian_synthesizes (label : Wire d r ≃ Fin n) (vertex : Fin (m + 1) → Fin d → F)
    (hzero : vertex 0 = 0) (copies : Fin r ≃ Fin (m + 1) × Fin k) (last : Fin (m + 1))
    (p : (HamiltonPath.cubeGraph vertex).Walk 0 last) (hp : p.IsHamiltonian) :
    Circuit.SynthesizesWithin
      (EncodedTarget.tableau label (vertex last) (ReplicatedTarget.repeated vertex copies)) (r + m) := by
  obtain ⟨cs, hlen, hx⟩ := hamiltonian_rows label vertex hzero copies last p hp
  simpa only [hlen] using ClassicalLift.synthesizes label cs (vertex last) _ hx

theorem hamiltonian_implies_synthesis (vertex : Fin (m + 1) → Fin d → F)
    (hzero : vertex 0 = 0) (last : Fin (m + 1))
    (hp : ∃ p : (HamiltonPath.cubeGraph vertex).Walk 0 last, p.IsHamiltonian) :
    Circuit.SynthesizesWithin (EncodedTarget.instanceTableau vertex last) (EncodedTarget.recorderCount m + m) := by
  obtain ⟨p, hp⟩ := hp
  exact hamiltonian_synthesizes (EncodedTarget.physicalLabel d (EncodedTarget.recorderCount m))
    vertex hzero (EncodedTarget.copies m) last p hp

/-- The actual bounded Clifford-synthesis instance is equivalent to the actual
Mathlib specified-endpoint Hamiltonian-path predicate in the induced cube graph.
Only the source instance's distinct vertices and zero start are hypotheses. -/
theorem synthesis_iff_hamiltonian (vertex : Fin (m + 1) → Fin d → F)
    (hv : Function.Injective vertex) (hzero : vertex 0 = 0) (last : Fin (m + 1)) :
    Circuit.SynthesizesWithin (EncodedTarget.instanceTableau vertex last) (EncodedTarget.recorderCount m + m) ↔
      ∃ p : (HamiltonPath.cubeGraph vertex).Walk 0 last, p.IsHamiltonian :=
  ⟨HamiltonPath.synthesis_implies_hamiltonian vertex hv hzero last,
    hamiltonian_implies_synthesis vertex hzero last⟩

end CliffordSynthesis.Reduction
