/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.MarkedGrid
public import GridHardness.Hamiltonian

/-!
# Grid Cycle

Hamiltonian cycles on finite induced integer grids with explicitly encoded points.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness
open CliffordComplexity CliffordSynthesis SimpleGraph
open GridProblems GridProblems.GridCode

abbrev CycleInputTy := Ty.list PointTy

/-- Arbitrary finite induced grid graphs, with no marked vertices. Empty
lists and repeated decoded coordinates are no-instances. -/
def GRID_HAMILTONIAN_CYCLE : Problem CycleInputTy.denote := fun l =>
  ∃ (m : Nat) (p : Fin (m + 1) → PointTy.denote),
    l = List.ofFn p ∧ Function.Injective (decoded ∘ p) ∧
      ∃ a, ∃ w : (IntegerGrid.graph (decoded ∘ p)).Walk a a, w.IsHamiltonianCycle

theorem cycle_source_input {m : Nat} (p : Fin (m + 1) → PointTy.denote) :
    GRID_HAMILTONIAN_CYCLE (List.ofFn p) ↔ Function.Injective (decoded ∘ p) ∧
      ∃ a, ∃ w : (IntegerGrid.graph (decoded ∘ p)).Walk a a, w.IsHamiltonianCycle := by
  constructor
  · rintro ⟨m', p', he, hp, hw⟩
    have hn := congrArg List.length he
    simp only [List.length_ofFn] at hn
    have hm : m = m' := by omega
    subst m'
    have hps : p = p' := List.ofFn_injective he
    subst p'
    exact ⟨hp, hw⟩
  · rintro ⟨hp, hw⟩
    exact ⟨m, p, rfl, hp, hw⟩

theorem empty_not_grid_cycle : ¬ GRID_HAMILTONIAN_CYCLE [] := by
  rintro ⟨m, p, he, _⟩
  have := congrArg List.length he
  simp at this

def reindexGrid {m : Nat} (p : Fin (m + 1) → PointTy.denote)
    (e : Equiv.Perm (Fin (m + 1))) :
    IntegerGrid.graph (decoded ∘ (p ∘ e)) ≃g IntegerGrid.graph (decoded ∘ p) where
  toEquiv := e
  map_rel_iff' := Iff.rfl

theorem grid_cycle_reindex {m : Nat} (p : Fin (m + 1) → PointTy.denote)
    (e : Equiv.Perm (Fin (m + 1))) :
    GRID_HAMILTONIAN_CYCLE (List.ofFn (p ∘ e)) ↔
      GRID_HAMILTONIAN_CYCLE (List.ofFn p) := by
  rw [cycle_source_input, cycle_source_input]
  apply and_congr
  · constructor
    · intro h i j hij
      have he := h (a₁ := e.symm i) (a₂ := e.symm j) (by simpa using hij)
      exact e.symm.injective he
    · intro h
      exact h.comp e.injective
  · exact exists_isHamiltonianCycle_iff_of_equiv e (fun _ _ => Iff.rfl)

theorem marked_implies_grid_cycle {x : InputTy.denote} (h : MARKED_GRID_CYCLE x) :
    GRID_HAMILTONIAN_CYCLE x.1 := by
  obtain ⟨m, p, last, rfl, hp, _, _, _, hc⟩ := h
  exact ⟨m, p, rfl, hp, hc⟩

theorem marked_of_guard_of_grid_cycle {x : InputTy.denote}
    (hg : markedGuard.eval x = true) (hc : GRID_HAMILTONIAN_CYCLE x.1) :
    MARKED_GRID_CYCLE x := by
  have hv : validCode.eval x = true := (Bool.and_eq_true_iff.mp hg).1
  obtain ⟨m, p, last, rfl, _⟩ := (validCode_correct x).mp hv
  obtain ⟨hp, hn, hd, ha⟩ := (markedGuard_eval p last).mp hg
  exact ⟨m, p, last, rfl, hp, hn, hd, ha, ((cycle_source_input p).mp hc).2⟩

/-- Some transposition of vertex zero, followed by a neighbour marking,
passes the guard on every Hamiltonian grid. The selection program will check
all these polynomially many candidates, rather than search for a cycle. -/
theorem exists_good_marking {m : Nat} (p : Fin (m + 1) → PointTy.denote)
    (hc : GRID_HAMILTONIAN_CYCLE (List.ofFn p)) :
    ∃ s t : Fin (m + 1), markedGuard.eval (input (p ∘ Equiv.swap 0 s) t) = true := by
  obtain ⟨hp, hcycle⟩ := (cycle_source_input p).mp hc
  obtain ⟨s, hs⟩ := grid_cycle_has_degree_two (decoded ∘ p) hp hcycle
  have hpos : 0 < (IntegerGrid.graph (decoded ∘ p)).degree s := by omega
  obtain ⟨v, hv⟩ := ((IntegerGrid.graph (decoded ∘ p)).degree_pos_iff_exists_adj s).mp hpos
  let e := Equiv.swap (0 : Fin (m + 1)) s
  refine ⟨s, e.symm v, (markedGuard_eval _ _).mpr ⟨hp.comp e.injective, ?_, ?_, ?_⟩⟩
  · obtain ⟨a, w, hw⟩ := hcycle
    have h := hw.isCycle.three_le_length
    rw [hw.length_eq] at h
    simpa using h
  · have hd := (reindexGrid p e).degree_eq 0
    exact hd.symm.trans (by
      change (IntegerGrid.graph (decoded ∘ p)).degree ((Equiv.swap 0 s) 0) = 2
      rw [Equiv.swap_apply_left, hs])
  · change IntegerGrid.manhattan (decoded (p (e 0))) (decoded (p (e (e.symm v)))) = 1
    rw [Equiv.apply_symm_apply]
    change IntegerGrid.manhattan (decoded (p ((Equiv.swap 0 s) 0))) (decoded (p v)) = 1
    rw [Equiv.swap_apply_left]
    exact hv

end GridHardness
