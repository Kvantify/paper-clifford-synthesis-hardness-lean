/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import CliffordSynthesis.HamiltonPath
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Cube Dimension

A connected cube subgraph with every coordinate varying has dimension
at most its number of vertices minus one.
-/

public section

namespace CliffordSynthesis.CubeDimension

open Planes (F)

variable {m d : Nat}

theorem walk_crosses (vertex : Fin (m + 1) → Fin d → F) {u v : Fin (m + 1)}
    (p : (HamiltonPath.cubeGraph vertex).Walk u v) (j : Fin d)
    (h : vertex u j ≠ vertex v j) :
    ∃ a b, (HamiltonPath.cubeGraph vertex).Adj a b ∧ vertex a j ≠ vertex b j := by
  induction p with
  | nil => exact False.elim (h rfl)
  | @cons u v w hadj p ih =>
    by_cases he : vertex u j = vertex v j
    · exact ih (by rwa [← he])
    · exact ⟨u, v, hadj, he⟩

theorem edge_unit (u v : Fin d → F) (he : hammingDist u v = 1) (j : Fin d)
    (hj : u j ≠ v j) : v - u = Pi.single j 1 := by
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp he
  have hjk : j = k := by
    have : j ∈ Finset.univ.filter (fun i => u i ≠ v i) := by simp [hj]
    rwa [hk, Finset.mem_singleton] at this
  subst k
  funext i
  by_cases hi : i = j
  · subst i
    have hf : ∀ a b : F, a ≠ b → b - a = 1 := by decide
    simpa using hf (u j) (v j) hj
  · have hv : u i = v i := by
      by_contra hn
      have : i ∈ Finset.univ.filter (fun i => u i ≠ v i) := by simp [hn]
      rw [hk, Finset.mem_singleton] at this
      exact hi this
    simp [hi, hv]

/-- The nonzero-index vertex rows span the entire cube when the graph is
connected, starts at zero, and no coordinate is constant. -/
theorem span_eq_top (vertex : Fin (m + 1) → Fin d → F) (hzero : vertex 0 = 0)
    (hc : (HamiltonPath.cubeGraph vertex).Connected)
    (hvar : ∀ j, ∃ u v, vertex u j ≠ vertex v j) :
    Submodule.span F (Set.range (fun i : Fin m => vertex i.succ)) = ⊤ := by
  let S := Submodule.span F (Set.range (fun i : Fin m => vertex i.succ))
  have hv : ∀ i, vertex i ∈ S := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hzero]
      exact S.zero_mem
    · exact Submodule.subset_span ⟨j, rfl⟩
  have hb : ∀ j, (Pi.basisFun F (Fin d)) j ∈ S := by
    intro j
    obtain ⟨u, v, h⟩ := hvar j
    obtain ⟨p⟩ := hc u v
    obtain ⟨a, b, he, hj⟩ := walk_crosses vertex p j h
    have hs := S.sub_mem (hv b) (hv a)
    rw [edge_unit (vertex a) (vertex b) he j hj] at hs
    simpa using hs
  apply le_antisymm le_top
  rw [← (Pi.basisFun F (Fin d)).span_eq]
  exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hb j)

theorem dimension_le (vertex : Fin (m + 1) → Fin d → F) (hzero : vertex 0 = 0)
    (hc : (HamiltonPath.cubeGraph vertex).Connected)
    (hvar : ∀ j, ∃ u v, vertex u j ≠ vertex v j) : d ≤ m := by
  simpa using finrank_le_of_span_eq_top (span_eq_top vertex hzero hc hvar)

end CliffordSynthesis.CubeDimension
