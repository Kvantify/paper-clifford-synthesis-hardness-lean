/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.IntegerGrid
public import CliffordSynthesis.CubeDimension
public import CliffordSynthesis.Reduction

/-!
# Grid Reduction

The concrete reduction from integer-grid vertices to the Boolean Clifford
target, including its correctness and coordinate-dimension bound.
-/

@[expose] public section

namespace CliffordSynthesis.GridReduction

open Planes (F)
open IntegerGrid (span normalized)

variable {m : Nat}

def dimension (point : Fin (m + 1) → Int × Int) : Nat :=
  span (fun i => (point i).1) + span (fun i => (point i).2)

def raw (point : Fin (m + 1) → Int × Int) (i : Fin (m + 1)) :
    Fin (span (fun i => (point i).1)) ⊕ Fin (span (fun i => (point i).2)) → Bool :=
  GridEmbedding.encode _ _ (normalized point i)

def vertex (point : Fin (m + 1) → Int × Int) (i : Fin (m + 1)) : Fin (dimension point) → F :=
  fun j => LocalChart.bit (GridEmbedding.translate (raw point 0) (raw point i) (finSumFinEquiv.symm j))

theorem hamming_reindex {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (e : α ≃ β) (u v : β → γ) : hammingDist (u ∘ e) (v ∘ e) = hammingDist u v := by
  simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem vertex_distance (point : Fin (m + 1) → Int × Int) (i j : Fin (m + 1)) :
    hammingDist (vertex point i) (vertex point j) = IntegerGrid.manhattan (point i) (point j) := by
  unfold vertex
  rw [hammingDist_comp (fun _ => LocalChart.bit) (fun _ => ClassicalLift.bit_injective)]
  exact (hamming_reindex finSumFinEquiv.symm
    (GridEmbedding.translate (raw point 0) (raw point i))
    (GridEmbedding.translate (raw point 0) (raw point j))).trans
    ((GridEmbedding.translate_distance _ _ _).trans (IntegerGrid.normalized_distance point i j))

theorem vertex_zero (point : Fin (m + 1) → Int × Int) : vertex point 0 = 0 := by
  funext j
  simp [vertex, GridEmbedding.translate, LocalChart.bit]

theorem vertex_injective (point : Fin (m + 1) → Int × Int) (hp : Function.Injective point) :
    Function.Injective (vertex point) := by
  intro i j h
  have hd := vertex_distance point i j
  rw [h, hammingDist_self] at hd
  apply hp
  unfold IntegerGrid.manhattan at hd
  apply Prod.ext <;> omega

theorem graph_eq (point : Fin (m + 1) → Int × Int) :
    HamiltonPath.cubeGraph (vertex point) = IntegerGrid.graph point := by
  ext i j
  exact congrArg (· = 1) (vertex_distance point i j) |>.to_iff

theorem raw_varies (point : Fin (m + 1) → Int × Int)
    (j : Fin (span (fun i => (point i).1)) ⊕ Fin (span (fun i => (point i).2))) :
    ∃ u v, raw point u j ≠ raw point v j := by
  have hcoord (f : Fin (m + 1) → Int) (j : Fin (span f)) :
      ∃ u v, GridEmbedding.unary (span f) (IntegerGrid.shift f u) j ≠
        GridEmbedding.unary (span f) (IntegerGrid.shift f v) j := by
    obtain ⟨u, _, hu⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty f
    obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
    have hu' : IntegerGrid.lower f = f u := hu
    have hv' : IntegerGrid.upper f = f v := hv
    have hmin : IntegerGrid.shift f u = 0 := by simp [IntegerGrid.shift, hu']
    have hmax : IntegerGrid.shift f v = span f := by simp [IntegerGrid.shift, span, hv']
    exact ⟨u, v, by simp [hmin, hmax, GridEmbedding.unary, j.isLt]⟩
  rcases j with j | j
  · exact hcoord (fun i => (point i).1) j
  · exact hcoord (fun i => (point i).2) j

theorem vertex_varies (point : Fin (m + 1) → Int × Int) (j : Fin (dimension point)) :
    ∃ u v, vertex point u j ≠ vertex point v j := by
  obtain ⟨u, v, h⟩ := raw_varies point (finSumFinEquiv.symm j)
  refine ⟨u, v, ?_⟩
  intro he
  have he' := ClassicalLift.bit_injective he
  simp only [GridEmbedding.translate] at he'
  cases hs : raw point 0 (finSumFinEquiv.symm j) <;> simp_all

/-- The exact dimension bound d ≤ M-1, including the case M=1. -/
theorem dimension_le (point : Fin (m + 1) → Int × Int) (hc : (IntegerGrid.graph point).Connected) :
    dimension point ≤ m := by
  apply CubeDimension.dimension_le (vertex point) (vertex_zero point)
  · rwa [graph_eq]
  · exact vertex_varies point

def target (point : Fin (m + 1) → Int × Int) (last : Fin (m + 1)) :
    Circuit.Tableau (dimension point + (1 + EncodedTarget.recorderCount m)) :=
  EncodedTarget.instanceTableau (vertex point) last

/-- Complete mathematical reduction correctness for the given integer-grid
coordinates and specified endpoints. No connectedness hypothesis is needed. -/
theorem synthesis_iff_hamiltonian (point : Fin (m + 1) → Int × Int)
    (hp : Function.Injective point) (last : Fin (m + 1)) :
    Circuit.SynthesizesWithin (target point last) (EncodedTarget.recorderCount m + m) ↔
      ∃ p : (IntegerGrid.graph point).Walk 0 last, p.IsHamiltonian := by
  change Circuit.SynthesizesWithin (EncodedTarget.instanceTableau (vertex point) last) _ ↔ _
  rw [Reduction.synthesis_iff_hamiltonian (vertex point) (vertex_injective point hp) (vertex_zero point)]
  rw [graph_eq]

theorem qubit_bound (point : Fin (m + 1) → Int × Int) (hc : (IntegerGrid.graph point).Connected) :
    dimension point + (1 + EncodedTarget.recorderCount m) ≤ 6 * m * m + 8 * m + 2 := by
  have hd := dimension_le point hc
  unfold EncodedTarget.recorderCount EncodedTarget.replication
  nlinarith

theorem threshold_eq (m : Nat) : EncodedTarget.recorderCount m + m = 6 * m * m + 8 * m + 1 := by
  unfold EncodedTarget.recorderCount EncodedTarget.replication
  ring

end CliffordSynthesis.GridReduction
