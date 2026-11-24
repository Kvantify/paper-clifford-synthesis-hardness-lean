/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.PlanarSatClausePorts
public import GridHardness.OrbitHamiltonian

/-!
# Planar SAT Backward

Extract a satisfying exact-one assignment from a Hamiltonian traversal of the SAT graph.
-/

public section

set_option backward.isDefEq.respectTransparency false

namespace GridHardness.PlanarSatBackward
open PlanarSatAssembly

/-- The global connectedness argument for a clause, after reading its actual
port choices. Wrong truth patterns create explicit proper cycles, including
the sixteen-vertex cycle containing the middle occurrence's XOR route. -/
theorem exactly_one_from_steps {V : Type*} (next : V → V) (ho : OneOrbit next)
    (C : Fin 12 → V) (X : Fin 3 → Fin 8 → V) (outside : V)
    (houtC : ∀ i, outside ≠ C i) (houtX : ∀ j i, outside ≠ X j i)
    (b : Fin 3 → Bool)
    (hB : ∀ j, next (C (clauseBottom j)) =
      if b j then C (![3, 7, 11] j) else X j 4)
    (hU : ∀ j, next (C (![2, 6, 10] j)) =
      if b j then C (clauseTop j) else C (![3, 7, 11] j))
    (hL0 : next (C 3) = C 6) (hL1 : next (C 7) = C 10)
    (hL2 : next (C 11) = C 2) (hT1 : next (C 5) = C 0)
    (hT2 : next (C 9) = C 4)
    (hX : ∀ j, b j = false → ∀ e : Fin 10, XorGadget.rightRoute e = true →
      next (X j (XorGadget.arc e).1) = X j (XorGadget.arc e).2)
    (hExit : ∀ j, b j = false → next (X j 7) = C (clauseTop j)) :
    ((List.finRange 3).filter b).length = 1 := by
  have h01 : ¬ (b 0 = true ∧ b 1 = true) := by
    rintro ⟨hb0, hb1⟩
    exact ho.not_closed_four (by simpa [clauseBottom, hb0] using hB 0)
      hL0 (by simpa [clauseTop, hb1] using hU 1) hT1
      ⟨houtC 0, houtC 3, houtC 6, houtC 5⟩
  have h12 : ¬ (b 1 = true ∧ b 2 = true) := by
    rintro ⟨hb1, hb2⟩
    exact ho.not_closed_four (by simpa [clauseBottom, hb1] using hB 1)
      hL1 (by simpa [clauseTop, hb2] using hU 2) hT2
      ⟨houtC 4, houtC 7, houtC 10, houtC 9⟩
  have hzero : ¬ (b 0 = false ∧ b 1 = false ∧ b 2 = false) := by
    rintro ⟨hb0, hb1, hb2⟩
    apply ho.not_closed_enumeration ![C 2, C 3, C 6, C 7, C 10, C 11] outside
    · intro i
      fin_cases i <;> exact houtC _
    · intro i
      fin_cases i
      · change next (C 2) = C 3
        simpa [hb0] using hU 0
      · exact hL0
      · change next (C 6) = C 7
        simpa [hb1] using hU 1
      · exact hL1
      · change next (C 10) = C 11
        simpa [hb2] using hU 2
      · exact hL2
  have h02 : ¬ (b 0 = true ∧ b 1 = false ∧ b 2 = true) := by
    rintro ⟨hb0, hb1, hb2⟩
    have hx40 := hX 1 hb1 5 (by decide)
    have hx01 := hX 1 hb1 0 (by decide)
    have hx15 := hX 1 hb1 1 (by decide)
    have hx56 := hX 1 hb1 7 (by decide)
    have hx62 := hX 1 hb1 8 (by decide)
    have hx23 := hX 1 hb1 3 (by decide)
    have hx37 := hX 1 hb1 4 (by decide)
    apply ho.not_closed_enumeration
      ![C 4, X 1 4, X 1 0, X 1 1, X 1 5, X 1 6, X 1 2, X 1 3,
        X 1 7, C 5, C 0, C 3, C 6, C 7, C 10, C 9] outside
    · intro i
      fin_cases i <;> first | exact houtC _ | exact houtX _ _
    · intro i
      fin_cases i
      · change next (C 4) = X 1 4
        simpa [clauseBottom, hb1] using hB 1
      · exact hx40
      · exact hx01
      · exact hx15
      · exact hx56
      · exact hx62
      · exact hx23
      · exact hx37
      · exact hExit 1 hb1
      · exact hT1
      · change next (C 0) = C 3
        simpa [clauseBottom, hb0] using hB 0
      · exact hL0
      · change next (C 6) = C 7
        simpa [hb1] using hU 1
      · exact hL1
      · change next (C 10) = C 9
        simpa [clauseTop, hb2] using hU 2
      · exact hT2
  have hbool : ∀ b : Fin 3 → Bool,
      ((List.finRange 3).filter b).length = 1 ↔
        ¬ (b 0 = true ∧ b 1 = true) ∧ ¬ (b 1 = true ∧ b 2 = true) ∧
        ¬ (b 0 = false ∧ b 1 = false ∧ b 2 = false) ∧
        ¬ (b 0 = true ∧ b 1 = false ∧ b 2 = true) := by decide
  exact (hbool b).mpr ⟨h01, h12, hzero, h02⟩

/-- Extracting a truth assignment from an actual Hamiltonian successor of the
assembled graph satisfies every clause. All port hypotheses above are proved
here from the concrete edge-list constructor. -/
theorem extractedAssignment_satisfies {n m : Nat} (φ : Formula n m)
    (next : Equiv.Perm (Vertex n m)) (ho : OneOrbit next)
    (ha : ∀ v, Adj φ v (next v)) : Satisfies φ (extractedAssignment φ next) := by
  intro c
  apply exactly_one_from_steps next ho (clause c) (fun j => xor (c, j)) (sent 0)
    (fun i => by simp [sent, clause])
    (fun j i => by simp [sent, PlanarSatAssembly.xor])
    (fun j => extractedAssignment φ next (φ c j))
  · exact clause_bottom_step φ next ho ha c
  · exact clause_upper_step φ next ho ha c
  · simpa [clauseSuccessors] using clause_successor_mem φ next ha c 3 (by decide)
  · simpa [clauseSuccessors] using clause_successor_mem φ next ha c 7 (by decide)
  · simpa [clauseSuccessors] using clause_successor_mem φ next ha c 11 (by decide)
  · simpa [clauseSuccessors] using clause_successor_mem φ next ha c 5 (by decide)
  · simpa [clauseSuccessors] using clause_successor_mem φ next ha c 9 (by decide)
  · intro j hj e he
    have hr := (extractedAssignment_false_iff φ next ho ha (c, j)).mp hj
    exact (PlanarSatXor.selection_true _ _ e).mp (by rw [hr]; exact he)
  · intro j hj
    exact (rightRoute_clause_links φ next ha (c, j)
      ((extractedAssignment_false_iff φ next ho ha (c, j)).mp hj)).2

theorem satisfiable_of_oneOrbit {n m : Nat} (φ : Formula n m)
    (next : Equiv.Perm (Vertex n m)) (ho : OneOrbit next)
    (ha : ∀ v, Adj φ v (next v)) : Satisfiable φ :=
  ⟨extractedAssignment φ next, extractedAssignment_satisfies φ next ho ha⟩

end GridHardness.PlanarSatBackward
