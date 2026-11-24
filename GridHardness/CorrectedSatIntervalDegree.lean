/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineRegistryIntervalDegree
public import GridHardness.CorrectedSatIntervalGraph

/-!
# Corrected SAT Interval Degree

Intrinsic directed degree bounds for the entire two-sided SAT insertion
sweep. Both the crossing schedule and its interval coverage are computed
internally; no additional graph-theoretic premise is required.
-/

public section

namespace GridHardness.CorrectedSatInterval
open XorLineRegistry XorLineSchedule
open CorrectedSatDegree (Bounds)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

theorem crossed_bounds {n : Nat} (s : IntervalState (n + 1))
    (height : Nat → Nat) (j : Nat) (h : Ready s height j)
    (hd : Bounds s.toFiniteGraph) : Bounds (crossed s height j h).toFiniteGraph :=
  s.crossRequests_bounds 0 (height j) _ _ _ hd

theorem next_bounds {n : Nat} (s : IntervalState (n + 1))
    (height : Nat → Nat) (j : Nat) (h : Ready s height j)
    (hd : Bounds s.toFiniteGraph) : Bounds (next s height j h).toFiniteGraph :=
  crossed_bounds s height j h hd

theorem run_bounds (height : Nat → Nat) (hinj : Function.Injective height)
    (hpos : ∀ i, 0 < height i) (n : Nat) : ∀ j (s : IntervalState n)
    (h : Ready s height j), Bounds s.toFiniteGraph →
      Bounds (run height hinj hpos n j s h) := by
  induction n with
  | zero => intro j s h hd; exact hd
  | succ n ih =>
    intro j s h hd
    exact ih (j + 1) (next s height j h) (next_ready s height hinj hpos j h)
      (next_bounds s height j h hd)

theorem initial_bounds {n m : Nat} (φ : PlanarSatAssembly.Formula n m) :
    Bounds (initialState φ).toFiniteGraph := CorrectedSatDegree.initial_bounds φ

theorem graph_bounds {n m : Nat} (φ : PlanarSatAssembly.Formula n m) :
    Bounds (graph φ) := run_bounds _ _ _ _ _ _ _ (initial_bounds φ)

theorem actual_bounds (x : CliffordComplexity.SatTy.denote) :
    Bounds (actualGraph x) := graph_bounds _

theorem positive_bounds (x : CliffordComplexity.SatTy.denote) :
    Bounds (positiveGraph x) := by
  unfold positiveGraph
  split
  · exact actual_bounds x
  · exact CorrectedSatDegree.invalid_bounds

end
end GridHardness.CorrectedSatInterval
