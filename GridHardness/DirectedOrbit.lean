/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.Logic.Function.Iterate

/-!
# Directed Orbit

The single-orbit condition for a successor map and consequences for closed subsets.
-/

@[expose] public section

namespace GridHardness

/-- The successor of a directed Hamiltonian cycle has one orbit. -/
def OneOrbit {V : Type*} (next : V → V) : Prop :=
  ∀ u v, ∃ n : Nat, (next^[n]) u = v

/-- A nonempty successor-closed set in one orbit contains every vertex. -/
theorem OneOrbit.closed_spans {V : Type*} {next : V → V} (h : OneOrbit next)
    {P : V → Prop} {a : V} (ha : P a) (hclosed : ∀ v, P v → P (next v)) : ∀ v, P v := by
  have hi : ∀ n, P ((next^[n]) a) := by
    intro n
    induction n with
    | zero => exact ha
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hclosed _ ih
  intro v
  obtain ⟨n, rfl⟩ := h a v
  exact hi n

/-- A proper four-cycle cannot be a component of a single spanning orbit.
Distinctness of the four vertices is unnecessary for this obstruction. -/
theorem OneOrbit.not_closed_four {V : Type*} {next : V → V} (h : OneOrbit next)
    {a b c d z : V} (hab : next a = b) (hbc : next b = c)
    (hcd : next c = d) (hda : next d = a)
    (hz : z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ d) : False := by
  have hc : ∀ v, v = a ∨ v = b ∨ v = c ∨ v = d →
      next v = a ∨ next v = b ∨ next v = c ∨ next v = d := by
    intro v hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl hab)
    · exact Or.inr (Or.inr (Or.inl hbc))
    · exact Or.inr (Or.inr (Or.inr hcd))
    · exact Or.inl hda
  have hv := h.closed_spans (P := fun v => v = a ∨ v = b ∨ v = c ∨ v = d)
    (Or.inl rfl) hc z
  rcases hv with ha | hb | hc | hd
  · exact hz.1 ha
  · exact hz.2.1 hb
  · exact hz.2.2.1 hc
  · exact hz.2.2.2 hd

end GridHardness
