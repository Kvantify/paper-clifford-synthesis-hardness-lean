/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

/-!
# Geometry

Finite induced integer-grid graphs and their Manhattan adjacency.
-/

@[expose] public section

namespace CliffordSynthesis.IntegerGrid
variable {m : Nat}

def manhattan (p q : Int × Int) : Nat := (p.1 - q.1).natAbs + (p.2 - q.2).natAbs

theorem manhattan_comm (p q : Int × Int) : manhattan p q = manhattan q p := by
  unfold manhattan
  omega

theorem manhattan_triangle (p q r : Int × Int) : manhattan p r ≤ manhattan p q + manhattan q r := by
  unfold manhattan
  omega

def graph (point : Fin (m + 1) → Int × Int) : SimpleGraph (Fin (m + 1)) where
  Adj u v := manhattan (point u) (point v) = 1
  symm := ⟨by intro u v h; rwa [manhattan_comm]⟩
  loopless := ⟨by intro u; simp [manhattan]⟩

/-- A grid walk changes Manhattan distance by at most one per edge. -/
theorem walk_distance (point : Fin (m + 1) → Int × Int) {u v : Fin (m + 1)}
    (p : (graph point).Walk u v) : manhattan (point u) (point v) ≤ p.length := by
  induction p with
  | nil => simp [manhattan]
  | @cons u v w hadj p ih =>
    simp only [SimpleGraph.Walk.length_cons]
    have ht := manhattan_triangle (point u) (point v) (point w)
    change manhattan (point u) (point v) = 1 at hadj
    omega

/-- Connectedness bounds distances independently of the magnitudes of the
binary-encoded integer coordinates. -/
theorem connected_distance (point : Fin (m + 1) → Int × Int) (hc : (graph point).Connected)
    (u v : Fin (m + 1)) : manhattan (point u) (point v) ≤ m := by
  obtain ⟨p, hp⟩ := hc.exists_isPath u v
  have hd := walk_distance point p
  have hl := hp.length_lt
  simp only [Fintype.card_fin] at hl
  omega

end CliffordSynthesis.IntegerGrid
