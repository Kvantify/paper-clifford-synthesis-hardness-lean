/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistryIntervalRun
public import GridHardness.CorrectedSatDegree

/-!
# XOR Line Registry Interval Degree

The two-sided interval registry preserves the directed degree bounds of
the SAT construction. The bounds use intrinsic finite cardinalities, so they
do not depend on an enumeration of the changing vertex type.
-/

public section

namespace GridHardness.XorLineRegistry.IntervalState
open XorLineSchedule
open XorWire.NetworkDegree (inDegree outDegree)
open CorrectedSatDegree (Bounds bounds_iff)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

variable {n : Nat}

/-- Selecting and splitting an actual residual interval preserves in-degree
at most two, out-degree at most two, and total directed degree at most three. -/
theorem cross_bounds (s : IntervalState n) (a : Fin n) (line height : Nat)
    (hc : s.Covered line height) (hd : Bounds s.toFiniteGraph) :
    Bounds (s.cross a line height hc).toFiniteGraph := by
  classical
  let _ : Fintype s.Vertex := Fintype.ofFinite _
  let _ : Fintype (s.cross a line height hc).Vertex := inferInstanceAs
    (Fintype ((s.positioned.registry.bundles (s.select line height hc).val).RefinedVertex
      (s.positioned.registry.xors.embed a)))
  apply (bounds_iff _).mpr
  have h := (bounds_iff s.toFiniteGraph).mp hd
  intro v
  exact (s.positioned.registry.bundles (s.select line height hc).val).refined_degree_bounds
    (s.positioned.registry.xors.embed a)
    (s.positioned.registry.xors.embed_injective a) (s.positioned.registry.xors.isolated a)
    (s.positioned.registry.xor_ne_source a (s.select line height hc).val)
    (s.positioned.registry.xor_ne_target a (s.select line height hc).val)
    (fun v => (h v).1) (fun v => (h v).2.1) (fun v => (h v).2.2) v

/-- The degree invariant holds after every actual crossing in a row. -/
theorem crossRequests_bounds (s : IntervalState n) (a : Fin n) (height : Nat)
    (requests : List Nat) (hn : requests.Nodup)
    (hc : ∀ j ∈ requests, s.Covered j height) (hd : Bounds s.toFiniteGraph) :
    Bounds (s.crossRequests a height requests hn hc).toFiniteGraph := by
  induction requests generalizing s with
  | nil => exact hd
  | cons i is ih =>
    exact ih (s.cross a i height (hc i (by simp)))
      (List.nodup_cons.mp hn).2 (s.cross_remaining_covered a height i is hn hc)
      (s.cross_bounds a i height _ hd)

/-- Retiring the current XOR changes only the registry, not the graph. -/
theorem retire_bounds (s : IntervalState (n + 1)) (line upper : Nat)
    (hfresh : ∀ b, (s.positioned.segments b).line ≠ line)
    (hd : Bounds s.toFiniteGraph) :
    Bounds (s.retire line upper hfresh).toFiniteGraph := hd

/-- An enumeration-dependent formulation for graph algorithms that use
finite sets of incoming and outgoing neighbors. -/
theorem degree_bounds (s : IntervalState n) [Fintype s.Vertex]
    (hd : Bounds s.toFiniteGraph) (v : s.Vertex) :
    inDegree s.adj v ≤ 2 ∧ outDegree s.adj v ≤ 2 ∧
      inDegree s.adj v + outDegree s.adj v ≤ 3 :=
  (bounds_iff _).mp hd v

end
end GridHardness.XorLineRegistry.IntervalState
