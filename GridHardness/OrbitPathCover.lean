/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.OrbitHamiltonian
public import GridHardness.OrbitSplicing
public import Mathlib.Data.Fintype.Sigma

/-!
# Orbit Path Cover

Expansion and contraction of arbitrary finite directed path covers.
Each base vertex is replaced by a nonempty path, whose length may depend
on the vertex. The endpoint wiring is preserved exactly. This is used to
compare gadget replacements with different numbers of internal vertices.
-/

@[expose] public section

namespace GridHardness.PathCover

abbrev Blocks {V : Type*} (size : V → Nat) := (v : V) × Fin (size v + 1)

def entry {V : Type*} (size : V → Nat) (v : V) : Blocks size := ⟨v, 0⟩
def last {V : Type*} (size : V → Nat) (v : V) : Blocks size := ⟨v, Fin.last (size v)⟩

/-- A successor follows every internal edge of the specified path cover. -/
def Follows {V : Type*} {size : V → Nat} (step : Blocks size → Blocks size) : Prop :=
  ∀ (v : V) (i : Fin (size v)), step ⟨v, i.castSucc⟩ = ⟨v, i.succ⟩

/-- The expanded successor advances within a path, then follows the base
successor to the first vertex of the next path. -/
def expand {V : Type*} (size : V → Nat) (next : V → V) : Blocks size → Blocks size :=
  fun ⟨v, i⟩ => if h : i.val < size v then ⟨v, ⟨i.val + 1, by omega⟩⟩
    else entry size (next v)

theorem expand_follows {V : Type*} (size : V → Nat) (next : V → V) :
    Follows (expand size next) := by
  intro v i
  simp [expand, i.isLt]
  apply Fin.ext
  rfl

@[simp] theorem expand_last {V : Type*} (size : V → Nat) (next : V → V) (v : V) :
    expand size next (last size v) = entry size (next v) := by
  simp [expand, last]

theorem reach_from_entry {V : Type*} {size : V → Nat}
    {step : Blocks size → Blocks size} (h : Follows step) (v : V)
    (i : Fin (size v + 1)) : StepReach step (entry size v) ⟨v, i⟩ := by
  induction i using Fin.induction with
  | zero => exact StepReach.refl _ _
  | succ i ih =>
    exact ih.trans ⟨1, h v i⟩

theorem reach_to_last {V : Type*} {size : V → Nat}
    {step : Blocks size → Blocks size} (h : Follows step) (v : V)
    (i : Fin (size v + 1)) : StepReach step ⟨v, i⟩ (last size v) := by
  induction i using Fin.reverseInduction with
  | last => exact StepReach.refl _ _
  | cast i ih =>
    exact (show StepReach step ⟨v, i.castSucc⟩ ⟨v, i.succ⟩ from ⟨1, h v i⟩).trans ih

theorem oneOrbit_expand {V : Type*} {next : V → V} (h : OneOrbit next)
    (size : V → Nat) : OneOrbit (expand size next) := by
  apply h.expand (entry size)
  · intro v
    exact (reach_to_last (expand_follows size next) v 0).trans
      ⟨1, expand_last size next v⟩
  · rintro ⟨v, i⟩
    exact ⟨next v, (reach_to_last (expand_follows size next) v i).trans
      ⟨1, expand_last size next v⟩⟩
  · rintro ⟨v, i⟩
    exact ⟨v, reach_from_entry (expand_follows size next) v i⟩

/-- Contract each path to one base vertex by reading the successor of its
last vertex. This definition does not assume that the contracted map spans. -/
def contract {V : Type*} {size : V → Nat} (step : Blocks size → Blocks size) : V → V :=
  fun v => (step (last size v)).1

theorem last_maps_to_entry {V : Type*} {size : V → Nat}
    {step : Blocks size → Blocks size} (hi : Function.Injective step)
    (hf : Follows step) (v : V) :
    step (last size v) = entry size (contract step v) := by
  generalize he : step (last size v) = w
  obtain ⟨u, j⟩ := w
  simp only [contract, he]
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
    have hs := hi (he.trans (hf u j).symm)
    have hv : v = u := congrArg Sigma.fst hs
    subst u
    have hj : Fin.last (size v) = j.castSucc := by
      simpa [last] using hs
    have hn := congrArg Fin.val hj
    have hlt := j.isLt
    simp only [Fin.val_last, Fin.val_castSucc] at hn
    omega

theorem step_projects {V : Type*} {size : V → Nat}
    {step : Blocks size → Blocks size} (hf : Follows step) (w : Blocks size) :
    (step w).1 = w.1 ∨ (step w).1 = contract step w.1 := by
  obtain ⟨v, i⟩ := w
  cases i using Fin.lastCases with
  | last => exact Or.inr rfl
  | cast i =>
    rw [hf v i]
    exact Or.inl rfl

theorem oneOrbit_contract {V : Type*} {size : V → Nat}
    {step : Blocks size → Blocks size} (ho : OneOrbit step) (hf : Follows step) :
    OneOrbit (contract step) :=
  ho.project Sigma.fst (fun v => ⟨entry size v, rfl⟩) (step_projects hf)

/-- Injectivity forces every path exit to enter a path at its first vertex.
Consequently the entire successor is exactly an expansion of its contraction. -/
theorem expand_contract {V : Type*} {size : V → Nat}
    {step : Blocks size → Blocks size} (hi : Function.Injective step)
    (hf : Follows step) : expand size (contract step) = step := by
  funext w
  obtain ⟨v, i⟩ := w
  cases i using Fin.lastCases with
  | last => exact (expand_last _ _ _).trans (last_maps_to_entry hi hf v).symm
  | cast i => exact (expand_follows _ _ v i).trans (hf v i).symm

@[simp] theorem contract_expand {V : Type*} (size : V → Nat) (next : V → V) :
    contract (expand size next) = next := by
  funext v
  simp [contract, entry]

/-- Directed Hamiltonicity after a fixed path cover is exactly Hamiltonicity
of the endpoint wiring. Internal edges and exit wiring are graph predicates,
not assumptions of Hamiltonicity. -/
theorem hamiltonian_iff {V : Type*} [Finite V] (size : V → Nat)
    (D : V → V → Prop) :
    (∃ next : Equiv.Perm V, OneOrbit next ∧ ∀ v, D v (next v)) ↔
      ∃ step : Equiv.Perm (Blocks size), OneOrbit step ∧ Follows step ∧
        ∀ v, D v (contract step v) := by
  constructor
  · rintro ⟨next, ho, ha⟩
    have he := oneOrbit_expand ho size
    refine ⟨Equiv.ofBijective _ he.bijective, he, expand_follows _ _, ?_⟩
    intro v
    change D v (contract (expand size next) v)
    simpa using ha v
  · rintro ⟨step, ho, hf, ha⟩
    have hc := oneOrbit_contract ho hf
    exact ⟨Equiv.ofBijective _ hc.bijective, hc, ha⟩

end GridHardness.PathCover
