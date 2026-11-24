/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWirePaths
public import GridHardness.AttachedGadget

/-!
# XOR Wire Replacement

Assemble XOR wire gadgets at embedded ports and define the inter-gadget wiring.
-/

@[expose] public section

namespace GridHardness.XorWire
open PathCover

def input (n : Nat) (_ : Unit) (choice : Bool) : Vertex n := entry n choice
def output (n : Nat) (_ : Unit) (choice : Bool) : Vertex n := exit n choice

def attached {O : Type*} (n : Nat) (outside : O → O → Prop)
    (enter : O → Bool → Prop) (leave : Bool → O → Prop) :
    (O ⊕ Vertex n) → (O ⊕ Vertex n) → Prop :=
  AttachedGadget.Adj outside (Adj n) (input n) (output n)
    (fun o (_ : Unit) s => enter o s) (fun (_ : Unit) s o => leave s o)

def wiring {O : Type*} (outside : O → O → Prop)
    (enter : O → Bool → Prop) (leave : Bool → O → Prop) (choice : Bool) :
    (O ⊕ Unit) → (O ⊕ Unit) → Prop :=
  AttachedGadget.Wiring outside (fun o (_ : Unit) s => enter o s)
    (fun (_ : Unit) s o => leave s o) (fun _ => choice)

theorem input_injective (n : Nat) : Function.Injective (fun p : Unit × Bool => input n p.1 p.2) := by
  rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
  cases a <;> cases b <;> simp_all [input, entry]

theorem output_injective (n : Nat) : Function.Injective (fun p : Unit × Bool => output n p.1 p.2) := by
  rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
  cases a <;> cases b <;> simp_all [output, exit]

theorem no_output_input_edge (n : Nat) (a b : Bool) : ¬Adj n (exit n a) (entry n b) := by
  have hlocal : ∀ a b : Bool, ¬∃ e : Fin 10,
      XorGadget.arc e = ((if a then 0 else 7), (if b then 3 else 4)) := by decide
  cases a <;> cases b <;>
    simp only [exit, entry, Bool.false_eq_true, ↓reduceIte, Adj, Fin.val_zero, Fin.val_last,
      Prod.fst, Prod.snd] <;>
    simp_all [hlocal]

theorem attached_isolated {O : Type*} (n : Nat) (outside : O → O → Prop)
    (enter : O → Bool → Prop) (leave : Bool → O → Prop)
    (step : Equiv.Perm (O ⊕ Vertex n))
    (ha : ∀ w, attached n outside enter leave w (step w)) :
    Isolated n step (Sum.inr : Vertex n → O ⊕ Vertex n) where
  internal := AttachedGadget.internal outside (Adj n) (input n) (output n) _ _ step ha
  outgoing := by
    intro u ht hf
    apply AttachedGadget.outgoing outside (Adj n) (input n) (output n) _ _ step ha u
    rintro ⟨⟩ s
    cases s
    · exact hf
    · exact ht
  incoming := by
    intro v ht hf
    apply AttachedGadget.incoming outside (Adj n) (input n) (output n) _ _ step ha v
    rintro ⟨⟩ s
    cases s
    · exact hf
    · exact ht

theorem attached_classification {O : Type*} (n : Nat) (outside : O → O → Prop)
    (enter : O → Bool → Prop) (leave : Bool → O → Prop)
    (step : Equiv.Perm (O ⊕ Vertex n)) (ho : OneOrbit step)
    (ha : ∀ w, attached n outside enter leave w (step w)) :
    ∃ choice : Bool, ((cover n choice).extend O).FollowedBy step := by
  classical
  obtain ⟨choice, hc⟩ := route_classification step ho Sum.inr Sum.inr_injective
    (attached_isolated n outside enter leave step ha)
  exact ⟨choice, (cover n choice).extend_followedBy step hc⟩

theorem attached_internalEdges {O : Type*} (n : Nat) (outside : O → O → Prop)
    (enter : O → Bool → Prop) (leave : Bool → O → Prop) (choice : Bool) :
    ((cover n choice).extend O).InternalEdges (attached n outside enter leave) := by
  apply Cover.extend_internalEdges
  exact cover_adjacent n choice

theorem attached_wiring {O : Type*} (n : Nat) (outside : O → O → Prop)
    (enter : O → Bool → Prop) (leave : Bool → O → Prop)
    (choice : Bool) (u v : O ⊕ Unit) :
    ((cover n choice).extend O).Wiring (attached n outside enter leave) u v ↔
      wiring outside enter leave choice u v := by
  apply AttachedGadget.cover_wiring outside (Adj n) (input n) (output n) _ _
    (input_injective n) (output_injective n) (fun _ => choice) (cover n choice)
  · rintro ⟨⟩; exact cover_first n choice
  · rintro ⟨⟩; exact cover_finish n choice
  · rintro ⟨⟩ ⟨⟩; exact no_output_input_edge n choice choice

/-- The complete attached wire has exactly the endpoint-wiring Hamiltonian
cycles associated with its two uniform route choices. -/
theorem attached_hamiltonian_iff {O : Type*} [Finite O] (n : Nat)
    (outside : O → O → Prop) (enter : O → Bool → Prop) (leave : Bool → O → Prop) :
    Hamiltonian (attached n outside enter leave) ↔
      ∃ choice : Bool, Hamiltonian (wiring outside enter leave choice) := by
  rw [hamiltonian_iff_wiring (fun choice => (cover n choice).extend O)
    (attached n outside enter leave) (attached_internalEdges n outside enter leave)
    (attached_classification n outside enter leave)]
  apply exists_congr
  intro choice
  unfold Hamiltonian
  apply exists_congr
  intro step
  exact and_congr_right (fun _ => forall_congr' (fun u =>
    attached_wiring n outside enter leave choice u (step u)))

/-- Replacing a single eight-vertex XOR by any nonempty serial XOR wire
preserves Hamiltonicity in every finite surrounding directed graph. -/
theorem stretch_iff {O : Type*} [Finite O] (n : Nat)
    (outside : O → O → Prop) (enter : O → Bool → Prop) (leave : Bool → O → Prop) :
    Hamiltonian (attached 0 outside enter leave) ↔
      Hamiltonian (attached n outside enter leave) := by
  rw [attached_hamiltonian_iff, attached_hamiltonian_iff]

/-- The zero-length extension is precisely one original XOR: no connecting
edges remain, and its sole section has the original ten directed arcs. -/
theorem zero_adj_iff (u v : Vertex 0) :
    Adj 0 u v ↔ ∃ e : Fin 10, XorGadget.arc e = (u.2, v.2) := by
  have hu : u.1 = 0 := by apply Fin.ext; have := u.1.isLt; simp
  have hv : v.1 = 0 := by apply Fin.ext; have := v.1.isLt; simp
  simp [Adj, hu, hv]

end GridHardness.XorWire
