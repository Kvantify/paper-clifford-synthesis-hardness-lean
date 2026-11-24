/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLinePorts
public import GridHardness.XorLineAttachment

/-!
# XOR Line Replacement

Exact graph-level refinement of one exclusive-or line across any finite
family of mandatory arcs. This preserves the original endpoint pairs, unlike
serial wire stretching. The compulsory arcs remain independent traversals.
-/

@[expose] public section

namespace GridHardness.XorLine
open PathCover

section
variable {O : Type*} (n : Nat) (outside : O → O → Prop)
variable (enter : O → Port n → Prop) (leave : Port n → O → Prop)

def attached : (O ⊕ Vertex n) → (O ⊕ Vertex n) → Prop :=
  XorLineAttachment.Adj outside (Adj n) (inputPort n) (outputPort n) enter leave

theorem attached_isolated (step : Equiv.Perm (O ⊕ Vertex n))
    (ha : ∀ w, attached n outside enter leave w (step w)) :
    Isolated n step Sum.inr where
  internal := XorLineAttachment.internal outside (Adj n) (inputPort n) (outputPort n)
    enter leave step ha
  outgoing := by
    intro u hu
    apply XorLineAttachment.outgoing outside (Adj n) (inputPort n) (outputPort n)
      enter leave step ha u
    intro p hp
    apply hu
    rw [hp]
    exact outputPort_isOutput n p
  incoming := by
    intro u hu
    apply XorLineAttachment.incoming outside (Adj n) (inputPort n) (outputPort n)
      enter leave step ha u
    intro p hp
    apply hu
    rw [hp]
    exact inputPort_isInput n p

theorem attached_hamiltonian_iff [Finite O] :
    Hamiltonian (attached n outside enter leave) ↔
      ∃ choice : Bool, Hamiltonian (XorLineAttachment.Wiring outside enter leave (selected choice)) := by
  apply XorLineAttachment.hamiltonian_iff_wiring outside (Adj n)
    (inputPort n) (outputPort n) enter leave (cover n) selected
    (inputPort_injective n) (outputPort_injective n)
    (cover_first_port n) (cover_finish_port n)
    (fun _ _ _ => no_output_input_edge n _ _) (cover_adjacent n)
  intro step ho ha
  classical
  exact route_classification step ho Sum.inr Sum.inr_injective
    (attached_isolated n outside enter leave step ha)

namespace Source

def attached : (O ⊕ Vertex n) → (O ⊕ Vertex n) → Prop :=
  XorLineAttachment.Adj outside (Adj n) (inputPort n) (outputPort n) enter leave

theorem attached_isolated (step : Equiv.Perm (O ⊕ Vertex n))
    (ha : ∀ w, attached n outside enter leave w (step w)) :
    Isolated n step Sum.inr where
  internal := XorLineAttachment.internal outside (Adj n) (inputPort n) (outputPort n)
    enter leave step ha
  outgoing := by
    intro u hu
    apply XorLineAttachment.outgoing outside (Adj n) (inputPort n) (outputPort n)
      enter leave step ha u
    intro p hp
    apply hu
    rw [hp]
    exact outputPort_isOutput n p
  incoming := by
    intro u hu
    apply XorLineAttachment.incoming outside (Adj n) (inputPort n) (outputPort n)
      enter leave step ha u
    intro p hp
    apply hu
    rw [hp]
    exact inputPort_isInput n p

theorem attached_hamiltonian_iff [Finite O] :
    Hamiltonian (attached n outside enter leave) ↔
      ∃ choice : Bool, Hamiltonian (XorLineAttachment.Wiring outside enter leave (selected choice)) := by
  apply XorLineAttachment.hamiltonian_iff_wiring outside (Adj n)
    (inputPort n) (outputPort n) enter leave (cover n) selected
    (inputPort_injective n) (outputPort_injective n)
    (cover_first_port n) (cover_finish_port n)
    (fun _ _ _ => no_output_input_edge n _ _) (cover_adjacent n)
  intro step ho ha
  classical
  exact route_classification step ho Sum.inr Sum.inr_injective
    (attached_isolated n outside enter leave step ha)

end Source

/-- Replace one XOR plus `n` actual, separately traversed mandatory arcs
with a constraint line containing `n+1` XOR sections. The theorem has no
assignment, degree, route, or Hamiltonian-traversal premise. All attachment
edges are arbitrary and explicitly included in the two compared graphs. -/
theorem refinement_iff [Finite O] :
    Hamiltonian (Source.attached n outside enter leave) ↔
      Hamiltonian (attached n outside enter leave) := by
  rw [Source.attached_hamiltonian_iff,attached_hamiltonian_iff]

end

theorem source_vertex_count (n : Nat) : Fintype.card (Source.Vertex n)=8+2*n := by
  simp [Source.Vertex,Nat.mul_comm]

theorem target_vertex_count (n : Nat) : Fintype.card (Vertex n)=8+10*n := by
  simp [Vertex]
  omega

end GridHardness.XorLine
