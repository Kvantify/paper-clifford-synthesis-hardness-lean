/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridProblems.Geometry
public import GridProblems.Validity

/-!
# Specified-endpoint Hamiltonian path on induced grid graphs

Specified-endpoint Hamiltonian path in a finite induced integer grid.
No hardness assumption and no Clifford-synthesis dependency occurs here.
-/

@[expose] public section

namespace GridProblems
open CliffordSynthesis CliffordComplexity GridCode

/-- Source predicate independent of the target and the reduction program.
Vertex zero is the specified start; the natural in the input specifies the end.
Coordinates are signed binary integers (differences of two binary naturals). -/
def GRID_HAMILTONIAN_PATH : Problem InputTy.denote := fun x =>
  ∃ (m : Nat) (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)),
    x = input p last ∧ Function.Injective (decoded ∘ p) ∧
      ∃ w : (IntegerGrid.graph (decoded ∘ p)).Walk 0 last, w.IsHamiltonian

theorem source_input {m : Nat} (p : Fin (m + 1) → PointTy.denote) (last : Fin (m + 1)) :
    GRID_HAMILTONIAN_PATH (input p last) ↔ Function.Injective (decoded ∘ p) ∧
      ∃ w : (IntegerGrid.graph (decoded ∘ p)).Walk 0 last, w.IsHamiltonian := by
  constructor
  · rintro ⟨m', p', last', he, hp, hw⟩
    have hn := congrArg (fun x : InputTy.denote => x.1.length) he
    simp only [input, List.length_ofFn] at hn
    have hm : m = m' := by omega
    subst m'
    have hps : p = p' := List.ofFn_injective (congrArg Prod.fst he)
    have hl : last = last' := Fin.ext (congrArg Prod.snd he)
    subst p'
    subst last'
    exact ⟨hp, hw⟩
  · rintro ⟨hp, hw⟩
    exact ⟨m, p, last, rfl, hp, hw⟩

theorem source_valid {x : InputTy.denote} (h : GRID_HAMILTONIAN_PATH x) : Valid x := by
  obtain ⟨m, p, last, he, hp, _⟩ := h
  exact ⟨m, p, last, he, hp⟩

end GridProblems
