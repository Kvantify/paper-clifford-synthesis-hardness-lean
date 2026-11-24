/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalDegree
public import GridHardness.CorrectedSatIntervalPermutationGraph

/-!
# Directed Incidence SATuration

A local criterion for completeness of a directed edge catalogue.
If the total incoming and outgoing degree is at most three, three distinct
directed incidences exhaust all arcs at the vertex. Incoming and outgoing
incidences are tagged separately, including when their neighbor is the
same. The permutation-sweep specialization supplies its proved degree
bound; it does not supply the three catalogue incidences.
-/

@[expose] public section

namespace GridHardness.DirectedIncidenceSaturation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Finite V] (D : V → V → Prop) (v : V)

/-- An incoming neighbor is tagged on the left; an outgoing neighbor on
the right. This counts directed incidences, rather than undirected neighbors. -/
abbrev Incidence := {u : V // D u v} ⊕ {u : V // D v u}

theorem incidence_card :
    Nat.card (Incidence D v) = Nat.card {u : V // D u v} + Nat.card {u : V // D v u} :=
  Nat.card_sum

/-- An injective list of as many incidences as the degree bound is
automatically exhaustive. The bound may be any natural number. -/
theorem exhaustive {k : Nat}
    (hd : Nat.card {u : V // D u v} + Nat.card {u : V // D v u} ≤ k)
    (w : Fin k → Incidence D v) (hw : Function.Injective w) :
    Function.Surjective w := by
  apply (hw.bijective_of_nat_card_le _).2
  simpa only [incidence_card,Nat.card_fin] using hd

theorem incoming_covered {k : Nat}
    (hd : Nat.card {u : V // D u v} + Nat.card {u : V // D v u} ≤ k)
    (w : Fin k → Incidence D v) (hw : Function.Injective w) (u : V) (hu : D u v) :
    ∃ i, w i = .inl ⟨u,hu⟩ :=
  exhaustive D v hd w hw (.inl ⟨u,hu⟩)

theorem outgoing_covered {k : Nat}
    (hd : Nat.card {u : V // D u v} + Nat.card {u : V // D v u} ≤ k)
    (w : Fin k → Incidence D v) (hw : Function.Injective w) (u : V) (hu : D v u) :
    ∃ i, w i = .inr ⟨u,hu⟩ :=
  exhaustive D v hd w hw (.inr ⟨u,hu⟩)

/-- A proposed edge classification applies in the actual direction of
the incidence. For a catalogue, use `C u v := ∃ e, endpoints e = (u,v)`. -/
def Classified (C : V → V → Prop) : Incidence D v → Prop
  | .inl u => C u.val v
  | .inr u => C v u.val

/-- It suffices to classify the supplied witnesses to classify every arc
incident with the saturated vertex. -/
theorem complete {k : Nat}
    (hd : Nat.card {u : V // D u v} + Nat.card {u : V // D v u} ≤ k)
    (w : Fin k → Incidence D v) (hw : Function.Injective w)
    (C : V → V → Prop) (hc : ∀ i, Classified D v C (w i)) :
    (∀ u, D u v → C u v) ∧ (∀ u, D v u → C v u) := by
  constructor
  · intro u hu
    obtain ⟨i,hi⟩ := incoming_covered D v hd w hw u hu
    have h := hc i
    rw [hi] at h
    exact h
  · intro u hu
    obtain ⟨i,hi⟩ := outgoing_covered D v hd w hw u hu
    have h := hc i
    rw [hi] at h
    exact h

/-- When the proposed classification also gives actual arcs, saturation
upgrades its local completeness to exact incoming and outgoing adjacency. -/
theorem adjacency_iff {k : Nat}
    (hd : Nat.card {u : V // D u v} + Nat.card {u : V // D v u} ≤ k)
    (w : Fin k → Incidence D v) (hw : Function.Injective w)
    (C : V → V → Prop) (hc : ∀ i, Classified D v C (w i))
    (hs : ∀ a b, C a b → D a b) :
    (∀ u, D u v ↔ C u v) ∧ (∀ u, D v u ↔ C v u) := by
  have h := complete D v hd w hw C hc
  exact ⟨fun u => ⟨h.1 u,hs u v⟩,fun u => ⟨h.2 u,hs v u⟩⟩

open CorrectedSatInterval PlanarSatAssembly

/-- The directed degree bound holds for any chosen occurrence permutation,
not only for the canonical wire order. -/
theorem permutation_bounds {n m : Nat} (φ : Formula n m)
    (p : Equiv.Perm (Fin (3 *m))) : CorrectedSatDegree.Bounds (PermutationGraph.graph φ p) :=
  run_bounds (permutationHeight p) (permutationHeight_injective p) (permutationHeight_pos p)
    (3*m) 0 (initialState φ) (PermutationGraph.initial_ready φ p) (initial_bounds φ)

/-- Three distinct directed incidences suffice at any vertex of the final
permutation sweep. Construction of those three incidences remains explicit. -/
theorem permutation_exhaustive {n m : Nat} (φ : Formula n m)
    (p : Equiv.Perm (Fin (3 *m))) (v : (PermutationGraph.graph φ p).Vertex)
    (w : Fin 3 → Incidence (PermutationGraph.graph φ p).adj v)
    (hw : Function.Injective w) : Function.Surjective w :=
  exhaustive _ v ((permutation_bounds φ p v).2.2) w hw

theorem permutation_complete {n m : Nat} (φ : Formula n m)
    (p : Equiv.Perm (Fin (3 *m))) (v : (PermutationGraph.graph φ p).Vertex)
    (w : Fin 3 → Incidence (PermutationGraph.graph φ p).adj v)
    (hw : Function.Injective w)
    (C : (PermutationGraph.graph φ p).Vertex → (PermutationGraph.graph φ p).Vertex → Prop)
    (hc : ∀ i, Classified (PermutationGraph.graph φ p).adj v C (w i)) :
    (∀ u, (PermutationGraph.graph φ p).adj u v → C u v) ∧
    (∀ u, (PermutationGraph.graph φ p).adj v u → C v u) :=
  complete _ v ((permutation_bounds φ p v).2.2) w hw C hc

end GridHardness.DirectedIncidenceSaturation
