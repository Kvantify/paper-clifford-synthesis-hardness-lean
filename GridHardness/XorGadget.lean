/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic
public import GridHardness.DirectedOrbit

/-!
# XOR Gadget

The directed XOR gadget in Plesník's construction, as redrawn in
Bosboom et al., *Edge Matching with Inequalities, Triangles, Unknown Shape,
and Two Players* (2020), Figure 7.

Vertices 0,1,2,3 run down the left column; 4,5,6,7 down the right.
The entry ports are 3 and 4; the exit ports are 0 and 7. This file proves
the local edge-selection contract. It does not claim the SAT construction,
crossover expansion, or correctness of the complete graph assembly.
-/

@[expose] public section

namespace GridHardness.XorGadget

def arc : Fin 10 → Fin 8 × Fin 8 :=
  ![(0, 1), (1, 5), (2, 1), (2, 3), (3, 7),
    (4, 0), (5, 4), (5, 6), (6, 2), (7, 6)]

abbrev Selection := Fin 10 → Bool

def inDegree (b : Selection) (v : Fin 8) : Nat :=
  ((List.finRange 10).filter (fun e => b e && decide ((arc e).2 = v))).length

def outDegree (b : Selection) (v : Fin 8) : Nat :=
  ((List.finRange 10).filter (fun e => b e && decide ((arc e).1 = v))).length

/-- Degree constraints induced by restricting a directed Hamiltonian cycle
to the gadget. Only entries may receive an edge from outside, and only exits
may send an edge outside. -/
def DegreeOK (b : Selection) : Prop :=
  (∀ v, inDegree b v ≤ 1 ∧ outDegree b v ≤ 1) ∧
  (∀ v, v ≠ 3 → v ≠ 4 → inDegree b v = 1) ∧
  (∀ v, v ≠ 0 → v ≠ 7 → outDegree b v = 1)

/-- The three directed four-cycles of the gadget. A Hamiltonian cycle in a
larger graph cannot contain any of them as a closed component. -/
def NoClosedComponent (b : Selection) : Prop :=
  ¬(b 0 = true ∧ b 1 = true ∧ b 6 = true ∧ b 5 = true) ∧
  ¬(b 2 = true ∧ b 1 = true ∧ b 7 = true ∧ b 8 = true) ∧
  ¬(b 3 = true ∧ b 4 = true ∧ b 9 = true ∧ b 8 = true)

def leftRoute : Selection := ![false, true, true, false, true, true, true, false, true, true]
def rightRoute : Selection := ![true, true, false, true, true, true, false, true, true, false]

instance (b : Selection) : Decidable (DegreeOK b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (b : Selection) : Decidable (NoClosedComponent b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- Kernel evaluation checks the finite XOR gadget and its boundary.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite XOR gadget and its boundary.
/-- Exhaustive kernel-checked classification of all 1024 edge selections.
The no-closed-component condition is essential; degree constraints alone
also admit spurious disconnected cycle covers. -/
theorem selection_iff : ∀ b : Selection,
    DegreeOK b ∧ NoClosedComponent b ↔ b = leftRoute ∨ b = rightRoute := by
  decide

/-- Exactly one of the two original edges is traversed. -/
theorem exclusive_or (b : Selection) (h : DegreeOK b ∧ NoClosedComponent b) :
    (inDegree b 3 = 0 ∧ outDegree b 0 = 0 ∧ inDegree b 4 = 1 ∧ outDegree b 7 = 1) ∨
    (inDegree b 3 = 1 ∧ outDegree b 0 = 1 ∧ inDegree b 4 = 0 ∧ outDegree b 7 = 0) := by
  obtain rfl | rfl := (selection_iff b).mp h <;> decide

def leftVertices : List (Fin 8) := [3, 7, 6, 2, 1, 5, 4, 0]
def rightVertices : List (Fin 8) := [4, 0, 1, 5, 6, 2, 3, 7]

def Uses (b : Selection) (u v : Fin 8) : Prop := ∃ e : Fin 10, b e = true ∧ arc e = (u, v)
instance (b : Selection) (u v : Fin 8) : Decidable (Uses b u v) :=
  inferInstanceAs (Decidable (∃ _e : Fin 10, _))

/-- The two classified selections really traverse every internal vertex
once along the intended directed path, rather than merely balancing degrees. -/
theorem left_route_hamiltonian : leftVertices.IsChain (Uses leftRoute) ∧
    ∀ v : Fin 8, leftVertices.count v = 1 := by decide

theorem right_route_hamiltonian : rightVertices.IsChain (Uses rightRoute) ∧
    ∀ v : Fin 8, rightVertices.count v = 1 := by decide

/-- The forbidden components are excluded by a global Hamiltonian successor
once there is a vertex outside this gadget. Thus the finite classification's
cycle condition follows from global connectivity, rather than being a promise
about the selected edges. -/
theorem noClosedComponent_of_oneOrbit {V : Type*} (next : V → V) (hnext : OneOrbit next)
    (embed : Fin 8 → V) (outside : V) (hout : ∀ v, outside ≠ embed v)
    (b : Selection)
    (hstep : ∀ e, b e = true → next (embed (arc e).1) = embed (arc e).2) :
    NoClosedComponent b := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1, h6, h5⟩
    exact hnext.not_closed_four (hstep 0 h0) (hstep 1 h1) (hstep 6 h6) (hstep 5 h5)
      ⟨hout 0, hout 1, hout 5, hout 4⟩
  · rintro ⟨h2, h1, h7, h8⟩
    exact hnext.not_closed_four (hstep 2 h2) (hstep 1 h1) (hstep 7 h7) (hstep 8 h8)
      ⟨hout 2, hout 1, hout 5, hout 6⟩
  · rintro ⟨h3, h4, h9, h8⟩
    exact hnext.not_closed_four (hstep 3 h3) (hstep 4 h4) (hstep 9 h9) (hstep 8 h8)
      ⟨hout 2, hout 3, hout 7, hout 6⟩

theorem selection_of_oneOrbit {V : Type*} (next : V → V) (hnext : OneOrbit next)
    (embed : Fin 8 → V) (outside : V) (hout : ∀ v, outside ≠ embed v)
    (b : Selection) (hdeg : DegreeOK b)
    (hstep : ∀ e, b e = true → next (embed (arc e).1) = embed (arc e).2) :
    b = leftRoute ∨ b = rightRoute :=
  (selection_iff b).mp ⟨hdeg, noClosedComponent_of_oneOrbit next hnext embed outside hout b hstep⟩

end GridHardness.XorGadget
