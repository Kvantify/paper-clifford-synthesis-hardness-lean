/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.GridInstance

/-!
# Bounded Grid

A bounded-window variant of the grid embedding.  The window has
width `2m` in each direction, where there are `m+1` vertices.  Consequently
constructing the cube never iterates over a binary-encoded coordinate value.
Inputs outside the window cannot have a Hamiltonian path.
-/

@[expose] public section

namespace CliffordSynthesis.BoundedGrid

open Planes (F)

variable {m : Nat}

def InWindow (point : Fin (m + 1) → Int × Int) : Prop :=
  ∀ i, (-(m : Int) ≤ (point i).1 - (point 0).1 ∧ (point i).1 - (point 0).1 ≤ m) ∧
    (-(m : Int) ≤ (point i).2 - (point 0).2 ∧ (point i).2 - (point 0).2 ≤ m)

instance (point : Fin (m + 1) → Int × Int) : Decidable (InWindow point) :=
  inferInstanceAs (Decidable (∀ _i, _ ∧ _))

def shifted (point : Fin (m + 1) → Int × Int) (i : Fin (m + 1)) : Nat × Nat :=
  (((point i).1 - (point 0).1 + m).toNat, ((point i).2 - (point 0).2 + m).toNat)

def raw (point : Fin (m + 1) → Int × Int) (i : Fin (m + 1)) :
    Fin (2 * m) ⊕ Fin (2 * m) → Bool :=
  GridEmbedding.encode (2 * m) (2 * m) (shifted point i)

def bits (point : Fin (m + 1) → Int × Int) (i : Fin (m + 1)) :
    Fin (2 * m + 2 * m) → Bool :=
  fun j => GridEmbedding.translate (raw point 0) (raw point i) (finSumFinEquiv.symm j)

def vertex (point : Fin (m + 1) → Int × Int) (i : Fin (m + 1)) :
    Fin (2 * m + 2 * m) → F := fun j => LocalChart.bit (bits point i j)

theorem shifted_bounds (point : Fin (m + 1) → Int × Int) (hw : InWindow point)
    (i : Fin (m + 1)) : (shifted point i).1 ≤ 2 * m ∧ (shifted point i).2 ≤ 2 * m := by
  have h := hw i
  unfold shifted
  constructor <;> omega

theorem bits_distance (point : Fin (m + 1) → Int × Int) (hw : InWindow point)
    (i j : Fin (m + 1)) :
    hammingDist (bits point i) (bits point j) = IntegerGrid.manhattan (point i) (point j) := by
  unfold bits
  refine (GridReduction.hamming_reindex finSumFinEquiv.symm
    (GridEmbedding.translate (raw point 0) (raw point i))
    (GridEmbedding.translate (raw point 0) (raw point j))).trans ?_
  rw [GridEmbedding.translate_distance]
  rw [raw, raw, GridEmbedding.encode_distance (shifted_bounds point hw i)
    (shifted_bounds point hw j)]
  have hi := hw i
  have hj := hw j
  unfold shifted IntegerGrid.manhattan
  dsimp
  omega

theorem vertex_distance (point : Fin (m + 1) → Int × Int) (hw : InWindow point)
    (i j : Fin (m + 1)) :
    hammingDist (vertex point i) (vertex point j) = IntegerGrid.manhattan (point i) (point j) := by
  unfold vertex
  rw [hammingDist_comp (fun _ => LocalChart.bit) (fun _ => ClassicalLift.bit_injective)]
  exact bits_distance point hw i j

theorem vertex_zero (point : Fin (m + 1) → Int × Int) : vertex point 0 = 0 := by
  funext j
  simp [vertex, bits, GridEmbedding.translate, LocalChart.bit]

theorem vertex_injective (point : Fin (m + 1) → Int × Int) (hw : InWindow point)
    (hp : Function.Injective point) : Function.Injective (vertex point) := by
  intro i j h
  have hd := vertex_distance point hw i j
  rw [h, hammingDist_self] at hd
  apply hp
  unfold IntegerGrid.manhattan at hd
  apply Prod.ext <;> omega

theorem graph_eq (point : Fin (m + 1) → Int × Int) (hw : InWindow point) :
    HamiltonPath.cubeGraph (vertex point) = IntegerGrid.graph point := by
  ext i j
  exact (congrArg (· = 1) (vertex_distance point hw i j)).to_iff

theorem hamiltonian_inWindow (point : Fin (m + 1) → Int × Int) (last : Fin (m + 1))
    (p : (IntegerGrid.graph point).Walk 0 last) (hp : p.IsHamiltonian) : InWindow point := by
  have hc := GridInstance.hamiltonian_connected point last p hp
  intro i
  have h := IntegerGrid.connected_distance point hc i 0
  simp only [IntegerGrid.manhattan] at h
  omega

def reduce (point : Fin (m + 1) → Int × Int) (last : Fin (m + 1)) : GridInstance.Instance :=
  if InWindow point then
    ⟨2 * m + 2 * m + (1 + EncodedTarget.recorderCount m),
      EncodedTarget.instanceTableau (vertex point) last, EncodedTarget.recorderCount m + m⟩
  else ⟨3, NoInstance.fanout, 1⟩

theorem correct (point : Fin (m + 1) → Int × Int) (hp : Function.Injective point)
    (last : Fin (m + 1)) : GridInstance.Accepts (reduce point last) ↔
      ∃ p : (IntegerGrid.graph point).Walk 0 last, p.IsHamiltonian := by
  by_cases hw : InWindow point
  · rw [reduce, ite_eq_left hw]
    change Circuit.SynthesizesWithin (EncodedTarget.instanceTableau (vertex point) last) _ ↔ _
    rw [Reduction.synthesis_iff_hamiltonian _ (vertex_injective point hw hp) (vertex_zero point),
      graph_eq point hw]
  · rw [reduce, ite_eq_right hw]
    change Circuit.SynthesizesWithin NoInstance.fanout 1 ↔ _
    exact iff_of_false NoInstance.fanout_no_instance
      (fun ⟨p, h⟩ => hw (hamiltonian_inWindow point last p h))

theorem qubit_bound (point : Fin (m + 1) → Int × Int) (last : Fin (m + 1)) :
    (reduce point last).qubits ≤ 6 * m * m + 11 * m + 3 := by
  unfold reduce
  split
  · simp only [EncodedTarget.recorderCount, EncodedTarget.replication]
    nlinarith
  · dsimp
    omega

end CliffordSynthesis.BoundedGrid
