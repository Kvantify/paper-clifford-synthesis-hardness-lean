/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatForwardChain
public import GridHardness.PlanarSatBackward
public import GridHardness.PositiveSatFinite

/-!
# Planar SAT Reduction

Global correctness of the concrete variable/clause/XOR construction.
The target is the actual edge-list graph from `PlanarSatAssembly.edges`.
No local degree, route, or assignment-consistency promise is assumed.

This is the construction before crossing XOR lines are expanded. Therefore
these theorems establish the Hamiltonian equivalence but do not assert that
the produced graph has a planar drawing.
-/

@[expose] public section

namespace GridHardness.PlanarSatReduction
open PlanarSatAssembly PlanarSatForward

def Hamiltonian {n m : Nat} (φ : Formula n m) : Prop :=
  ∃ next : Equiv.Perm (Vertex n m), OneOrbit next ∧ ∀ v, Adj φ v (next v)

/-- A satisfying assignment yields an explicitly spliced spanning cycle.
Empty formulas are included: the three sentinels form the cycle. -/
theorem hamiltonian_of_satisfiable {n m : Nat} (φ : Formula n m)
    (h : Satisfiable φ) : Hamiltonian φ := by
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨picked, hpicked⟩ := exists_picked φ σ hσ
  have hn : order φ σ picked ≠ [] := by simp [order]
  apply oneOrbit_of_cyclic_list (Adj φ) (order φ σ picked)
    (order_nodup φ σ picked hpicked) (order_covers φ σ picked hpicked) hn
    (order_chain φ σ picked)
  have hc := order_closing_edge φ σ picked ((order φ σ picked).getLast hn) (by simp [List.getLast?_eq_some_getLast hn])
  simpa [order] using hc

/-- Both directions refer to the constructed graph itself, with no extra
gadget traversal assumptions in the Hamiltonian target. -/
theorem correct {n m : Nat} (φ : Formula n m) : Satisfiable φ ↔ Hamiltonian φ := by
  constructor
  · exact hamiltonian_of_satisfiable φ
  · rintro ⟨next, ho, ha⟩
    exact PlanarSatBackward.satisfiable_of_oneOrbit φ next ho ha

/-- Encode positive one-in-three SAT with repeated occurrences and unused variable slots. -/
theorem positiveSat_correct (x : CliffordComplexity.SatTy.denote)
    (hw : ∀ c ∈ x, c.length = 3) (hp : ∀ c ∈ x, ∀ p ∈ c, p.2 = true) :
    CliffordComplexity.Concrete.MONOTONE_ONE_IN_THREE_SAT3 x ↔ Hamiltonian (finiteFormula x) :=
  (finiteFormula_correct x hw hp).symm.trans (correct (finiteFormula x))

end GridHardness.PlanarSatReduction
