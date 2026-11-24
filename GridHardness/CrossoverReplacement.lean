/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.AttachedGadget
public import GridHardness.PlanarSatCrossoverRoutes

/-!
# Crossover Replacement

Graph-level use of the verified crossover routes. A crossover is
attached to an arbitrary outside graph via its eight named boundary ports.
The resulting Hamiltonian cycles are characterized by their endpoint wiring.
-/

@[expose] public section

namespace GridHardness.PlanarSatCrossover
open PathCover

def input (component choice : Bool) : Vertex :=
  if component then verticalEntry choice else horizontalEntry choice

def output (component choice : Bool) : Vertex :=
  if component then verticalExit choice else horizontalExit choice

def routes (choice : Bool → Bool) (component : Bool) : List Vertex :=
  if component then verticalPath (choice true)
    else horizontalPath (choice false) (choice true)

theorem route_certificate (choice : Bool → Bool) (b : Bool) :
    (routes choice b).IsChain Adj ∧
    (routes choice b).head? = some (input b (choice b)) ∧
    (routes choice b).getLast? = some (output b (choice b)) ∧
    0 < (routes choice b).length := by
  obtain ⟨hh, hv, he, hx, hve, hvx, hl, hvl, _⟩ :=
    path_certificate (choice false) (choice true)
  cases b
  · exact ⟨hh, he, hx, by simp only [routes, Bool.false_eq_true, ↓reduceIte, hl]; omega⟩
  · exact ⟨hv, hve, hvx, by simp only [routes, ↓reduceIte, hvl]; omega⟩

theorem routes_nonempty (choice : Bool → Bool) : ∀ b, routes choice b ≠ [] := by
  intro b h
  have hh := (route_certificate choice b).2.2.2
  rw [h] at hh
  exact Nat.not_lt_zero _ hh

theorem routes_count (choice : Bool → Bool) (v : Vertex) :
    (routes choice false).count v + (routes choice true).count v = 1 :=
  (path_certificate (choice false) (choice true)).2.2.2.2.2.2.2.2 v

noncomputable def cover (choice : Bool → Bool) : Cover Bool Vertex :=
  TwoLists.cover (routes choice) (routes_nonempty choice) (routes_count choice)

theorem cover_first (choice : Bool → Bool) (b : Bool) :
    (cover choice).first b = input b (choice b) := by
  change (TwoLists.cover _ _ _).first b = _
  rw [TwoLists.first_eq]
  have h := (route_certificate choice b).2.1
  rw [List.head?_eq_some_head (routes_nonempty choice b)] at h
  exact Option.some.inj h

theorem cover_finish (choice : Bool → Bool) (b : Bool) :
    (cover choice).finish b = output b (choice b) := by
  change (TwoLists.cover _ _ _).finish b = _
  rw [TwoLists.finish_eq]
  have h := (route_certificate choice b).2.2.1
  rw [List.getLast?_eq_some_getLast (routes_nonempty choice b)] at h
  exact Option.some.inj h

theorem input_injective : Function.Injective (fun p : Bool × Bool => input p.1 p.2) := by
  decide

theorem output_injective : Function.Injective (fun p : Bool × Bool => output p.1 p.2) := by
  decide

theorem input_mem_entries : ∀ b s, input b s ∈ entries := by decide
theorem output_mem_exits : ∀ b s, output b s ∈ exits := by decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
theorem no_output_input_edge : ∀ b s c t, ¬Adj (output b s) (input c t) := by decide

def attached {O : Type*} (outside : O → O → Prop)
    (enter : O → Bool → Bool → Prop) (leave : Bool → Bool → O → Prop) :
    (O ⊕ Vertex) → (O ⊕ Vertex) → Prop :=
  AttachedGadget.Adj outside Adj input output enter leave

theorem attached_isolated {O : Type*} (outside : O → O → Prop)
    (enter : O → Bool → Bool → Prop) (leave : Bool → Bool → O → Prop)
    (step : Equiv.Perm (O ⊕ Vertex))
    (ha : ∀ w, attached outside enter leave w (step w)) :
    Isolated step (Sum.inr : Vertex → O ⊕ Vertex) where
  internal := AttachedGadget.internal outside Adj input output enter leave step ha
  outgoing := by
    intro u hu
    apply AttachedGadget.outgoing outside Adj input output enter leave step ha u
    intro b s he
    exact hu (he ▸ output_mem_exits b s)
  incoming := by
    intro v hv
    apply AttachedGadget.incoming outside Adj input output enter leave step ha v
    intro b s he
    exact hv (he ▸ input_mem_entries b s)

theorem attached_classification {O : Type*} (outside : O → O → Prop)
    (enter : O → Bool → Bool → Prop) (leave : Bool → Bool → O → Prop)
    (step : Equiv.Perm (O ⊕ Vertex)) (ho : OneOrbit step)
    (ha : ∀ w, attached outside enter leave w (step w)) :
    ∃ choice : Bool → Bool, ((cover choice).extend O).FollowedBy step := by
  classical
  obtain ⟨left, top, hh, hv, _⟩ := route_classification step ho Sum.inr Sum.inr_injective
    (attached_isolated outside enter leave step ha)
  let choice : Bool → Bool := fun b => if b then top else left
  refine ⟨choice, (cover choice).extend_followedBy step ?_⟩
  change (cover choice).InternalEdges (fun u v => step (Sum.inr u) = Sum.inr v)
  refine TwoLists.internalEdges (routes choice) (routes_nonempty choice)
    (routes_count choice) (fun u v => step (Sum.inr u) = Sum.inr v) ?_
  intro b
  cases b
  · simpa only [routes, choice, Bool.false_eq_true, ↓reduceIte] using hh
  · simpa only [routes, choice, ↓reduceIte] using hv

theorem attached_internalEdges {O : Type*} (outside : O → O → Prop)
    (enter : O → Bool → Bool → Prop) (leave : Bool → Bool → O → Prop)
    (choice : Bool → Bool) :
    ((cover choice).extend O).InternalEdges (attached outside enter leave) := by
  apply Cover.extend_internalEdges
  exact TwoLists.internalEdges _ _ _ Adj (fun b => (route_certificate choice b).1)

theorem attached_wiring {O : Type*} (outside : O → O → Prop)
    (enter : O → Bool → Bool → Prop) (leave : Bool → Bool → O → Prop)
    (choice : Bool → Bool) (u v : O ⊕ Bool) :
    ((cover choice).extend O).Wiring (attached outside enter leave) u v ↔
      AttachedGadget.Wiring outside enter leave choice u v :=
  AttachedGadget.cover_wiring outside Adj input output enter leave input_injective
    output_injective choice (cover choice) (cover_first choice) (cover_finish choice)
    (fun i j => no_output_input_edge i (choice i) j (choice j)) u v

/-- Exact characterization of the complete attached graph, including a
single global spanning cycle. The source of choices is the local graph proof. -/
theorem attached_hamiltonian_iff {O : Type*} [Finite O] (outside : O → O → Prop)
    (enter : O → Bool → Bool → Prop) (leave : Bool → Bool → O → Prop) :
    PathCover.Hamiltonian (attached outside enter leave) ↔
      ∃ choice : Bool → Bool,
        PathCover.Hamiltonian (AttachedGadget.Wiring outside enter leave choice) := by
  rw [PathCover.hamiltonian_iff_wiring (fun choice => (cover choice).extend O)
    (attached outside enter leave) (attached_internalEdges outside enter leave)
    (attached_classification outside enter leave)]
  apply exists_congr
  intro choice
  unfold PathCover.Hamiltonian
  apply exists_congr
  intro step
  exact and_congr_right (fun _ => forall_congr' (fun u =>
    attached_wiring outside enter leave choice u (step u)))

end GridHardness.PlanarSatCrossover
