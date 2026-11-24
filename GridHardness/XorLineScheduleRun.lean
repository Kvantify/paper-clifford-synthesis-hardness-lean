/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorLineScheduleStep

/-!
# XOR Line Schedule Run

Iterated graph refinement. A plan names actual currently
isolated XOR sections; each step proves the isolation needed by the next.
This is not a claim that an arbitrary plan yields a planar graph.
-/

@[expose] public section

namespace GridHardness.XorLineSchedule

/-- After crossing labels `a,b`, later moves can name any untouched XOR or
one of the five new sections, with their exact inherited identities. -/
inductive Plan : Type → Type 1 where
  | done {I : Type} : Plan I
  | cross {I : Type} (a b : I) (distinct : a≠b)
      (rest : Plan (Family.NextIndex a b)) : Plan I

def Plan.length : {I : Type} → Plan I → Nat
  | _, .done => 0
  | _, .cross _ _ _ rest => rest.length+1

structure FiniteGraph where
  Vertex : Type
  finite : Finite Vertex
  adj : Vertex → Vertex → Prop

attribute [instance] FiniteGraph.finite

/-- A structural recursion on the supplied list of concrete moves. No SAT
assignment or Hamiltonian cycle is an input to the constructed graph. -/
def run : {I : Type} → Plan I → {V : Type} → [Finite V] →
    (D : V → V → Prop) → Family D I → FiniteGraph
  | _, .done, V, hV, D, _ => ⟨V,hV,D⟩
  | _, .cross a b _ rest, _, _, _, f => run rest (f.step a b) (f.next a b)

theorem run_correct {I : Type} (p : Plan I) :
    ∀ {V : Type} [Finite V] (D : V → V → Prop) (f : Family D I),
      PathCover.Hamiltonian D ↔ PathCover.Hamiltonian (run p D f).adj := by
  induction p with
  | done => intros; rfl
  | cross a b hab rest ih =>
    intro V hV D f
    exact (f.step_correct a b hab).trans (ih (f.step a b) (f.next a b))

/-- Every move adds exactly forty vertices. This is a size theorem;
it is not a certificate for computing a geometric crossing schedule. -/
theorem run_vertex_count {I : Type} (p : Plan I) :
    ∀ {V : Type} [Finite V] (D : V → V → Prop) (f : Family D I),
      Nat.card (run p D f).Vertex=Nat.card V+40*p.length := by
  induction p with
  | done => intros; simp [run,Plan.length]
  | cross a b hab rest ih =>
    intro V hV D f
    classical
    letI : Fintype V := Fintype.ofFinite V
    change Nat.card (run rest (f.step a b) (f.next a b)).Vertex=_
    rw [ih (f.step a b) (f.next a b),f.step_vertex_count a,Nat.card_eq_fintype_card]
    simp only [Plan.length]
    omega

end GridHardness.XorLineSchedule
