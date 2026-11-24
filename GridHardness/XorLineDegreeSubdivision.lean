/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineScheduleSubdivision
public import GridHardness.XorWirePortDegree

/-!
# XOR Line Degree Subdivision

Simultaneous subdivision of distinct arcs preserves degree bounds.
Old-neighbor injections make the argument independent of any Hamiltonian cycle.
-/

@[expose] public section

namespace GridHardness.XorLineSchedule.Subdivision.Degree
open XorWire.NetworkDegree (inDegree outDegree)
set_option autoImplicit false
variable {V I : Type*} [Fintype V] [Fintype I]

def predecessor (s : I → V) : Vertex V I → V
  | .inl u => u
  | .inr (i, _) => s i

def successor (t : I → V) : Vertex V I → V
  | .inl u => u
  | .inr (i, _) => t i

theorem old_in_le (D : V → V → Prop) (s t : I → V)
    (hs : Function.Injective s) (hedge : ∀ i, D (s i) (t i)) (v : V) :
    inDegree (Adj D s t) (.inl v) ≤ inDegree D v := by
  classical
  unfold inDegree
  apply Finset.card_le_card_of_injOn (predecessor s)
  · intro u hu
    have ha := (Finset.mem_filter.mp hu).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    cases u with
    | inl u => exact ha.1
    | inr u => simpa only [predecessor, ha.2] using hedge u.1
  · intro u hu w hw he
    have ha := (Finset.mem_filter.mp hu).2
    have hb := (Finset.mem_filter.mp hw).2
    rcases u with u | ⟨i, b⟩ <;> rcases w with w | ⟨j, c⟩
    · exact congrArg Sum.inl he
    · exact False.elim (ha.2 ⟨j, he, hb.2⟩)
    · exact False.elim (hb.2 ⟨i, he.symm, ha.2⟩)
    · exact congrArg Sum.inr (Prod.ext (hs he) (ha.1.trans hb.1.symm))

theorem old_out_le (D : V → V → Prop) (s t : I → V)
    (ht : Function.Injective t) (hedge : ∀ i, D (s i) (t i)) (v : V) :
    outDegree (Adj D s t) (.inl v) ≤ outDegree D v := by
  classical
  unfold outDegree
  apply Finset.card_le_card_of_injOn (successor t)
  · intro u hu
    have ha := (Finset.mem_filter.mp hu).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    cases u with
    | inl u => exact ha.1
    | inr u => simpa only [successor, ha.1] using hedge u.1
  · intro u hu w hw he
    have ha := (Finset.mem_filter.mp hu).2
    have hb := (Finset.mem_filter.mp hw).2
    rcases u with u | ⟨i, b⟩ <;> rcases w with w | ⟨j, c⟩
    · exact congrArg Sum.inl he
    · exact False.elim (ha.2 ⟨j, hb.1, he⟩)
    · exact False.elim (hb.2 ⟨i, ha.1, he.symm⟩)
    · exact congrArg Sum.inr (Prod.ext (ht he) (ha.2.trans hb.2.symm))

theorem fresh_in_le_one (D : V → V → Prop) (s t : I → V) (i : I) (b : Bool) :
    inDegree (Adj D s t) (.inr (i, b)) ≤ 1 := by
  classical
  have hu : ∀ u, Adj D s t u (.inr (i, b)) →
      u = if b then .inr (i, false) else .inl (s i) := by
    rintro (u | ⟨j, c⟩) h
    · obtain ⟨hu, rfl⟩ := h
      exact congrArg Sum.inl hu
    · obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  unfold inDegree
  apply Finset.card_le_one.mpr
  intro a ha c hc
  exact (hu a (Finset.mem_filter.mp ha).2).trans (hu c (Finset.mem_filter.mp hc).2).symm

theorem fresh_out_le_one (D : V → V → Prop) (s t : I → V) (i : I) (b : Bool) :
    outDegree (Adj D s t) (.inr (i, b)) ≤ 1 := by
  classical
  have hu : ∀ u, Adj D s t (.inr (i, b)) u →
      u = if b then .inl (t i) else .inr (i, true) := by
    rintro (u | ⟨j, c⟩) h
    · obtain ⟨rfl, hu⟩ := h
      exact congrArg Sum.inl hu
    · obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  unfold outDegree
  apply Finset.card_le_one.mpr
  intro a ha c hc
  exact (hu a (Finset.mem_filter.mp ha).2).trans (hu c (Finset.mem_filter.mp hc).2).symm

/-- Both directed bounds and the stronger total-degree-three bound survive. -/
theorem degree_bounds (D : V → V → Prop) (s t : I → V)
    (hs : Function.Injective s) (ht : Function.Injective t) (hedge : ∀ i, D (s i) (t i))
    (hd : ∀ v, inDegree D v ≤ 2 ∧ outDegree D v ≤ 2 ∧ inDegree D v + outDegree D v ≤ 3)
    (v : Vertex V I) :
    inDegree (Adj D s t) v ≤ 2 ∧ outDegree (Adj D s t) v ≤ 2 ∧
      inDegree (Adj D s t) v + outDegree (Adj D s t) v ≤ 3 := by
  cases v with
  | inl v =>
    have hi := old_in_le D s t hs hedge v
    have ho := old_out_le D s t ht hedge v
    have hb := hd v
    omega
  | inr p =>
    rcases p with ⟨i, b⟩
    have hi := fresh_in_le_one D s t i b
    have ho := fresh_out_le_one D s t i b
    omega

end GridHardness.XorLineSchedule.Subdivision.Degree
