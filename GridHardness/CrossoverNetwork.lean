/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.GadgetNetwork
public import GridHardness.SingleCrossover

/-!
# Crossover Network

Simultaneously replace any finite collection of disjoint two-XOR cells
by planar crossover gadgets. Links may connect the cells arbitrarily; their
route choices are extracted from the actual ambient Hamiltonian cycle.
-/

@[expose] public section

namespace GridHardness.TwoXorGadget
open PathCover

section
variable {O C : Type*}
variable (outside : O → O → Prop)
variable (enter : O → C → Bool → Bool → Prop)
variable (leave : C → Bool → Bool → O → Prop)
variable (link : C → Bool → Bool → C → Bool → Bool → Prop)

def network : (O ⊕ (C × Vertex)) → (O ⊕ (C × Vertex)) → Prop :=
  GadgetNetwork.Adj outside Adj input output enter leave link

theorem network_isolated (step : Equiv.Perm (O ⊕ (C × Vertex)))
    (ha : ∀ w, network outside enter leave link w (step w)) (c : C) :
    Isolated step (fun w => Sum.inr (c, w)) where
  internal := GadgetNetwork.internal outside Adj input output enter leave link step ha c
  outgoing := by
    intro u hu
    apply GadgetNetwork.outgoing outside Adj input output enter leave link step ha c u
    intro b s he
    exact hu (he ▸ output_mem_exits b s)
  incoming := by
    intro v hv
    apply GadgetNetwork.incoming outside Adj input output enter leave link step ha c v
    intro b s he
    exact hv (he ▸ input_mem_entries b s)

theorem network_classification (step : Equiv.Perm (O ⊕ (C × Vertex)))
    (ho : OneOrbit step) (ha : ∀ w, network outside enter leave link w (step w))
    (c : C) : ∃ choice : Bool → Bool,
      (cover choice).InternalEdges (fun u v => step (Sum.inr (c, u)) = Sum.inr (c, v)) := by
  classical
  obtain ⟨left, top, hh, hv, _⟩ := route_classification step ho (fun w => Sum.inr (c, w))
    (GadgetNetwork.cell_injective c) (network_isolated outside enter leave link step ha c)
  let choice : Bool → Bool := fun b => if b then top else left
  refine ⟨choice, ?_⟩
  change (TwoLists.cover _ _ _).InternalEdges _
  apply TwoLists.internalEdges
  intro b
  cases b
  · simpa only [routes, choice, Bool.false_eq_true, ↓reduceIte] using hh
  · simpa only [routes, choice, ↓reduceIte] using hv

theorem network_hamiltonian_iff [Finite O] [Finite C] :
    Hamiltonian (network outside enter leave link) ↔
      ∃ choice : C → Bool → Bool,
        Hamiltonian (GadgetNetwork.Wiring outside enter leave link choice) := by
  exact GadgetNetwork.hamiltonian_iff_wiring outside Adj input output enter leave link cover
    input_injective output_injective cover_first cover_finish no_output_input_edge
    (fun choice => TwoLists.internalEdges _ _ _ Adj (fun b => (route_certificate choice b).1))
    (network_classification outside enter leave link)

end
end GridHardness.TwoXorGadget

namespace GridHardness.PlanarSatCrossover
open PathCover

section
variable {O C : Type*}
variable (outside : O → O → Prop)
variable (enter : O → C → Bool → Bool → Prop)
variable (leave : C → Bool → Bool → O → Prop)
variable (link : C → Bool → Bool → C → Bool → Bool → Prop)

def network : (O ⊕ (C × Vertex)) → (O ⊕ (C × Vertex)) → Prop :=
  GadgetNetwork.Adj outside Adj input output enter leave link

theorem network_isolated (step : Equiv.Perm (O ⊕ (C × Vertex)))
    (ha : ∀ w, network outside enter leave link w (step w)) (c : C) :
    Isolated step (fun w => Sum.inr (c, w)) where
  internal := GadgetNetwork.internal outside Adj input output enter leave link step ha c
  outgoing := by
    intro u hu
    apply GadgetNetwork.outgoing outside Adj input output enter leave link step ha c u
    intro b s he
    exact hu (he ▸ output_mem_exits b s)
  incoming := by
    intro v hv
    apply GadgetNetwork.incoming outside Adj input output enter leave link step ha c v
    intro b s he
    exact hv (he ▸ input_mem_entries b s)

theorem network_classification (step : Equiv.Perm (O ⊕ (C × Vertex)))
    (ho : OneOrbit step) (ha : ∀ w, network outside enter leave link w (step w))
    (c : C) : ∃ choice : Bool → Bool,
      (cover choice).InternalEdges (fun u v => step (Sum.inr (c, u)) = Sum.inr (c, v)) := by
  classical
  obtain ⟨left, top, hh, hv, _⟩ := route_classification step ho (fun w => Sum.inr (c, w))
    (GadgetNetwork.cell_injective c) (network_isolated outside enter leave link step ha c)
  let choice : Bool → Bool := fun b => if b then top else left
  refine ⟨choice, ?_⟩
  change (TwoLists.cover _ _ _).InternalEdges _
  apply TwoLists.internalEdges
  intro b
  cases b
  · simpa only [routes, choice, Bool.false_eq_true, ↓reduceIte] using hh
  · simpa only [routes, choice, ↓reduceIte] using hv

theorem network_hamiltonian_iff [Finite O] [Finite C] :
    Hamiltonian (network outside enter leave link) ↔
      ∃ choice : C → Bool → Bool,
        Hamiltonian (GadgetNetwork.Wiring outside enter leave link choice) := by
  exact GadgetNetwork.hamiltonian_iff_wiring outside Adj input output enter leave link cover
    input_injective output_injective cover_first cover_finish no_output_input_edge
    (fun choice => TwoLists.internalEdges _ _ _ Adj (fun b => (route_certificate choice b).1))
    (network_classification outside enter leave link)

end
end GridHardness.PlanarSatCrossover

namespace GridHardness

/-- Unconditional graph-level correctness for any finite network of marked,
disjoint crossover cells. The same explicit boundary links are used on both
sides. This theorem does not assert that arbitrary links already have a planar
geometric drawing; that is a separate construction. -/
theorem crossover_network_correct {O C : Type*} [Finite O] [Finite C]
    (outside : O → O → Prop)
    (enter : O → C → Bool → Bool → Prop)
    (leave : C → Bool → Bool → O → Prop)
    (link : C → Bool → Bool → C → Bool → Bool → Prop) :
    PathCover.Hamiltonian (TwoXorGadget.network outside enter leave link) ↔
    PathCover.Hamiltonian (PlanarSatCrossover.network outside enter leave link) := by
  rw [TwoXorGadget.network_hamiltonian_iff, PlanarSatCrossover.network_hamiltonian_iff]

/-- Each replacement adds exactly forty vertices. -/
theorem crossover_network_vertex_count {O C : Type*} [Fintype O] [Fintype C] :
    Fintype.card (O ⊕ (C × PlanarSatCrossover.Vertex)) =
      Fintype.card (O ⊕ (C × TwoXorGadget.Vertex)) + 40 * Fintype.card C := by
  have h16 : Fintype.card TwoXorGadget.Vertex = 16 := by decide
  have h56 : Fintype.card PlanarSatCrossover.Vertex = 56 := by decide
  simp only [Fintype.card_sum, Fintype.card_prod, h16, h56]
  omega

end GridHardness
