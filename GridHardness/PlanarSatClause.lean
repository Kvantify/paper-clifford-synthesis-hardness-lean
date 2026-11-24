/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.DirectedOrbit
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

/-!
# Planar SAT Clause

The positive one-in-three clause gadget in Bosboom et al. (2020),
Figure 9(b). Its twelve vertices are three groups `(B,T,U,L)`, numbered
from top to bottom. `B → T` is the right edge connected to the literal's
XOR line. `U,L` form the left-hand ring. Vertex 12 is a temporary return
vertex used only for the finite local certificate, not an extra gadget vertex.

The main contract `selection_of_oneOrbit` uses the actual global spanning
orbit to exclude disconnected cycle covers. Thus its conclusion does not
assume the desired local Hamiltonian traversal.
-/

@[expose] public section

namespace GridHardness.PlanarSatClause

abbrev Choices := Fin 6 → Bool

/-- The six choices are the outgoing branches of the three `B` vertices,
followed by the outgoing branches of the three `U` vertices. -/
def next (b : Choices) : Fin 13 → Fin 13 :=
  ![if b 0 then 1 else 3, 12, if b 3 then 1 else 3, 6,
    if b 1 then 5 else 7, 0, if b 4 then 5 else 7, 10,
    if b 2 then 9 else 11, 4, if b 5 then 9 else 11, 2, 8]

def route0 : Choices := ![false, true, true, true, false, false]
def route1 : Choices := ![true, false, true, false, true, false]
def route2 : Choices := ![true, true, false, false, false, true]

/-- The directed graph before connecting its three right edges to XOR lines. -/
def arcs : List (Fin 12 × Fin 12) :=
  [(0, 1), (0, 3), (2, 1), (2, 3), (3, 6),
   (4, 5), (4, 7), (5, 0), (6, 5), (6, 7), (7, 10),
   (8, 9), (8, 11), (9, 4), (10, 9), (10, 11), (11, 2)]

def Adj (u v : Fin 12) : Prop := (u, v) ∈ arcs
instance : DecidableRel Adj := fun u v => inferInstanceAs (Decidable ((u, v) ∈ arcs))

def order : Fin 3 → Fin 12 → Fin 12 :=
  ![![8, 9, 4, 5, 0, 3, 6, 7, 10, 11, 2, 1],
    ![8, 9, 4, 7, 10, 11, 2, 3, 6, 5, 0, 1],
    ![8, 11, 2, 3, 6, 7, 10, 9, 4, 5, 0, 1]]

theorem order_bijective (i : Fin 3) : Function.Bijective (order i) := by
  fin_cases i <;> decide

/-- Explicit Hamiltonian paths, needed to assemble a global witness without
searching for a cycle or making any choice depending on satisfiability. -/
theorem order_certificate (i : Fin 3) :
    order i 0 = 8 ∧ order i 11 = 1 ∧
    ∀ j : Fin 11, Adj (order i j.castSucc) (order i j.succ) := by
  fin_cases i <;> decide

/-- Right edge `j` is used by the path precisely when `j` is not the
satisfied literal. -/
theorem order_right_edge (i j : Fin 3) :
    (∃ k : Fin 11, (order i k.castSucc, order i k.succ) =
      (![0, 4, 8] j, ![1, 5, 9] j)) ↔ j ≠ i := by
  fin_cases i <;> fin_cases j <;> decide

def traversal (b : Choices) : List (Fin 13) :=
  (List.range 13).map (fun n => (next b)^[n] 12)

def trapped (b : Choices) : Finset (Fin 13) :=
  Finset.univ.filter (fun v => v ∉ traversal b)

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
/-- A kernel-checked finite classification of all 64 successor choices.
Every injective choice is an intended route or has a proper closed component.
The latter alternative is later excluded using global Hamiltonicity. -/
theorem classify : ∀ b : Choices, Function.Injective (next b) →
    b = route0 ∨ b = route1 ∨ b = route2 ∨
      ((trapped b).Nonempty ∧ 12 ∉ trapped b ∧
        ∀ v ∈ trapped b, next b v ∈ trapped b) := by
  decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
-- Kernel evaluation checks the finite gadget and its boundary cases.
/-- All three routes visit every internal vertex once, enter at vertex 8,
and exit at vertex 1. The three right-edge selections are precisely the
three ways of making two right edges present and one absent. -/
theorem route_certificates :
    ∀ b ∈ [route0, route1, route2],
      Function.Injective (next b) ∧
      (∀ v : Fin 13, (traversal b).count v = 1) ∧
      (next b)^[13] 12 = 12 ∧
      ((List.finRange 3).filter (fun i => !(b i.castSucc.castSucc.castSucc))).length = 1 := by
  decide

-- Kernel evaluation checks the finite gadget and its boundary cases.
set_option maxRecDepth 65536 in
/-- The two temporary boundary edges are the unique edges to their targets. -/
theorem boundary_targets : ∀ b : Choices, ∀ v : Fin 13,
    (next b v = 12 ↔ v = 1) ∧ (next b v = 8 ↔ v = 12) := by
  decide

/-- Local one-incoming-edge constraints follow from global injectivity;
they need not be asserted as an extra gadget promise. -/
theorem next_injective_of_embedding {V : Type*} (succ : V → V)
    (hsucc : Function.Injective succ)
    (embed : Fin 13 → V) (hinj : Function.Injective embed)
    (b : Choices)
    (hstep : ∀ v, v ≠ 1 → v ≠ 12 → succ (embed v) = embed (next b v)) :
    Function.Injective (next b) := by
  intro v w heq
  by_cases hv1 : v = 1
  · subst v
    exact ((boundary_targets b w).1.mp (heq.symm.trans (by simp [next]))).symm
  by_cases hv12 : v = 12
  · subst v
    exact ((boundary_targets b w).2.mp (heq.symm.trans (by simp [next]))).symm
  have hw1 : w ≠ 1 := by
    intro h
    subst w
    exact hv1 ((boundary_targets b v).1.mp (heq.trans (by simp [next])))
  have hw12 : w ≠ 12 := by
    intro h
    subst w
    exact hv12 ((boundary_targets b v).2.mp (heq.trans (by simp [next])))
  exact hinj (hsucc ((hstep v hv1 hv12).trans ((congrArg embed heq).trans
    (hstep w hw1 hw12).symm)))

/-- In a global one-orbit successor, the internal successor choices must
be one of the three Hamiltonian paths. The injectivity assumption is the
ordinary one-incoming-edge constraint, and is independent of connectivity. -/
theorem selection_of_oneOrbit {V : Type*} (succ : V → V) (horbit : OneOrbit succ)
    (embed : Fin 13 → V) (hinj : Function.Injective embed)
    (b : Choices) (hdegree : Function.Injective (next b))
    (hstep : ∀ v, v ≠ 1 → v ≠ 12 → succ (embed v) = embed (next b v)) :
    b = route0 ∨ b = route1 ∨ b = route2 := by
  rcases classify b hdegree with h | h | h | ⟨hne, hout, hclosed⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · obtain ⟨a, ha⟩ := hne
    have hclosed' : ∀ w, (∃ v ∈ trapped b, embed v = w) →
        ∃ v ∈ trapped b, embed v = succ w := by
      rintro w ⟨v, hv, rfl⟩
      have hv12 : v ≠ 12 := fun h => hout (h ▸ hv)
      have hv1 : v ≠ 1 := by
        intro h
        have := hclosed v hv
        subst v
        exact hout (by simpa [next] using this)
      exact ⟨next b v, hclosed v hv, (hstep v hv1 hv12).symm⟩
    obtain ⟨v, hv, hve⟩ := horbit.closed_spans (P := fun w => ∃ v ∈ trapped b, embed v = w)
      ⟨a, ha, rfl⟩ hclosed' (embed 12)
    exact False.elim (hout (hinj hve ▸ hv))

/-- A present variable edge excludes the corresponding clause right edge.
Consequently the gadget's three paths express exactly-one satisfaction. -/
theorem exactly_one_of_oneOrbit {V : Type*} (succ : V → V) (horbit : OneOrbit succ)
    (embed : Fin 13 → V) (hinj : Function.Injective embed)
    (b : Choices) (hdegree : Function.Injective (next b))
    (hstep : ∀ v, v ≠ 1 → v ≠ 12 → succ (embed v) = embed (next b v)) :
    ((List.finRange 3).filter (fun i => !(b i.castSucc.castSucc.castSucc))).length = 1 := by
  rcases selection_of_oneOrbit succ horbit embed hinj b hdegree hstep with rfl | rfl | rfl <;>
    decide

theorem selection_of_permutation {V : Type*} (succ : Equiv.Perm V)
    (horbit : OneOrbit succ) (embed : Fin 13 → V) (hinj : Function.Injective embed)
    (b : Choices)
    (hstep : ∀ v, v ≠ 1 → v ≠ 12 → succ (embed v) = embed (next b v)) :
    b = route0 ∨ b = route1 ∨ b = route2 :=
  selection_of_oneOrbit succ horbit embed hinj b
    (next_injective_of_embedding succ succ.injective embed hinj b hstep) hstep

end GridHardness.PlanarSatClause
