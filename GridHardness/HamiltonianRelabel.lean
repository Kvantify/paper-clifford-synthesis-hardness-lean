/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GadgetReplacement

/-!
# Hamiltonian Relabel

Transport Hamiltonian cycles and paths along graph isomorphisms.
-/

public section

namespace GridHardness.PathCover

theorem hamiltonian_relabel {V W : Type*} (D : V → V → Prop) (E : W → W → Prop)
    (e : V ≃ W) (he : ∀ u v, D u v → E (e u) (e v)) :
    Hamiltonian D → Hamiltonian E := by
  rintro ⟨step, ho, ha⟩
  let next : Equiv.Perm W := e.symm.trans (step.trans e)
  have hs : ∀ u, next (e u) = e (step u) := by intro u; simp [next]
  refine ⟨next, ho.transport e hs, ?_⟩
  intro w
  obtain ⟨u, rfl⟩ := e.surjective w
  rw [hs]
  exact he u (step u) (ha u)

/-- Directed Hamiltonicity is invariant under an exact relabelling of the
vertex type, with no cardinality or nonemptiness assumptions. -/
theorem hamiltonian_relabel_iff {V W : Type*} (D : V → V → Prop) (E : W → W → Prop)
    (e : V ≃ W) (he : ∀ u v, D u v ↔ E (e u) (e v)) :
    Hamiltonian D ↔ Hamiltonian E := by
  constructor
  · exact hamiltonian_relabel D E e (fun u v => (he u v).mp)
  · apply hamiltonian_relabel E D e.symm
    intro u v h
    apply (he (e.symm u) (e.symm v)).mpr
    simpa using h

end GridHardness.PathCover
