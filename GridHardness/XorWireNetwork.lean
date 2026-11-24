/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWireReplacement
public import GridHardness.GadgetNetwork

/-!
# XOR Wire Network

Simultaneous stretching of every XOR wire in a finite network. All
cell-to-cell connections are actual graph edges and all wire choices are
extracted from an ambient Hamiltonian cycle.
-/

@[expose] public section

namespace GridHardness.XorWire
open PathCover

section
variable {O C : Type*}
variable (outside : O → O → Prop)
variable (enter : O → C → Bool → Prop)
variable (leave : C → Bool → O → Prop)
variable (link : C → Bool → C → Bool → Prop)

def network (n : Nat) : (O ⊕ (C × Vertex n)) → (O ⊕ (C × Vertex n)) → Prop :=
  GadgetNetwork.Adj outside (Adj n) (input n) (output n)
    (fun o c (_ : Unit) s => enter o c s)
    (fun c (_ : Unit) s o => leave c s o)
    (fun c (_ : Unit) s d (_ : Unit) t => link c s d t)

def networkWiring (choice : C → Unit → Bool) :
    (O ⊕ (C × Unit)) → (O ⊕ (C × Unit)) → Prop :=
  GadgetNetwork.Wiring outside
    (fun o c (_ : Unit) s => enter o c s)
    (fun c (_ : Unit) s o => leave c s o)
    (fun c (_ : Unit) s d (_ : Unit) t => link c s d t) choice

theorem network_isolated (n : Nat) (step : Equiv.Perm (O ⊕ (C × Vertex n)))
    (ha : ∀ w, network outside enter leave link n w (step w)) (c : C) :
    Isolated n step (fun w => Sum.inr (c, w)) where
  internal := GadgetNetwork.internal outside (Adj n) (input n) (output n) _ _ _ step ha c
  outgoing := by
    intro u ht hf
    apply GadgetNetwork.outgoing outside (Adj n) (input n) (output n) _ _ _ step ha c u
    rintro ⟨⟩ s
    cases s
    · exact hf
    · exact ht
  incoming := by
    intro v ht hf
    apply GadgetNetwork.incoming outside (Adj n) (input n) (output n) _ _ _ step ha c v
    rintro ⟨⟩ s
    cases s
    · exact hf
    · exact ht

theorem network_classification (n : Nat) (step : Equiv.Perm (O ⊕ (C × Vertex n)))
    (ho : OneOrbit step) (ha : ∀ w, network outside enter leave link n w (step w))
    (c : C) : ∃ choice : Unit → Bool,
      (cover n (choice ())).InternalEdges
        (fun u v => step (Sum.inr (c, u)) = Sum.inr (c, v)) := by
  classical
  obtain ⟨choice, hc⟩ := route_classification step ho (fun w => Sum.inr (c, w))
    (GadgetNetwork.cell_injective c) (network_isolated outside enter leave link n step ha c)
  exact ⟨fun _ => choice, hc⟩

theorem network_hamiltonian_iff [Finite O] [Finite C] (n : Nat) :
    Hamiltonian (network outside enter leave link n) ↔
      ∃ choice : C → Unit → Bool, Hamiltonian (networkWiring outside enter leave link choice) := by
  apply GadgetNetwork.hamiltonian_iff_wiring outside (Adj n) (input n) (output n) _ _ _
    (fun choice => cover n (choice ())) (input_injective n) (output_injective n)
  · intro choice b
    cases b
    exact cover_first n (choice ())
  · intro choice b
    cases b
    exact cover_finish n (choice ())
  · rintro ⟨⟩ s ⟨⟩ t
    exact no_output_input_edge n s t
  · intro choice
    exact cover_adjacent n (choice ())
  · exact network_classification outside enter leave link n

/-- Any finite network of XORs can be stretched simultaneously to any
other uniform nonempty wire length without changing Hamiltonicity. -/
theorem network_stretch_iff [Finite O] [Finite C] (n m : Nat) :
    Hamiltonian (network outside enter leave link n) ↔
      Hamiltonian (network outside enter leave link m) := by
  rw [network_hamiltonian_iff, network_hamiltonian_iff]

end

theorem network_vertex_count {O C : Type*} [Fintype O] [Fintype C] (n : Nat) :
    Fintype.card (O ⊕ (C × Vertex n)) =
      Fintype.card O + Fintype.card C * ((n + 1) * 8) := by
  simp [Vertex]

end GridHardness.XorWire
