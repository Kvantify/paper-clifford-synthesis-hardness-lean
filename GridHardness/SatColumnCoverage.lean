/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatResidualDrawing
public import GridHardness.SatVerticalDrawing

/-!
# SAT Column Coverage

Every active column has extrema, and every cell either lies at an
extremum or has a consecutive neighbor on that side. These finite-order
facts account for the boundary attachments of the vertical route family.
-/

public section

namespace GridHardness.SatColumnCoverage
open SatCrossingRouting SatCrossingRetirement.Segments
set_option autoImplicit false

variable {N : Nat} (p : Equiv.Perm (Fin N))

theorem extrema (i : Fin N) (h : ¬ EmptyColumn p i) :
    (∃ j, FirstInColumn p i j) ∧ (∃ j, LastInColumn p i j) := by
  classical
  have hn : ({j : Fin N | Active p i j} : Set (Fin N)).Nonempty := by
    simpa only [EmptyColumn,not_forall,not_not,Set.nonempty_def,Set.mem_ofPred_eq] using h
  obtain ⟨j,hj,hmin⟩ := Set.exists_min_image _ p (Set.toFinite _) hn
  obtain ⟨k,hk,hmax⟩ := Set.exists_max_image _ p (Set.toFinite _) hn
  exact ⟨⟨j,hj,hmin⟩,⟨k,hk,hmax⟩⟩

theorem lower (i j : Fin N) (hj : Active p i j) :
    FirstInColumn p i j ∨ ∃ k, Consecutive p i k j := by
  classical
  by_cases hfirst : FirstInColumn p i j
  · exact Or.inl hfirst
  · right
    have hn : ({k : Fin N | Active p i k ∧ p k < p j} : Set (Fin N)).Nonempty := by
      by_contra he
      apply hfirst
      refine ⟨hj,fun k hk => ?_⟩
      by_contra hle
      exact he ⟨k,hk,lt_of_not_ge hle⟩
    obtain ⟨k,⟨hk,hkj⟩,hmax⟩ := Set.exists_max_image _ p (Set.toFinite _) hn
    refine ⟨k,hk,hj,hkj,fun l hl hkl => ?_⟩
    by_contra hle
    exact (not_lt_of_ge (hmax l ⟨hl,lt_of_not_ge hle⟩)) hkl

theorem upper (i j : Fin N) (hj : Active p i j) :
    LastInColumn p i j ∨ ∃ k, Consecutive p i j k := by
  classical
  by_cases hlast : LastInColumn p i j
  · exact Or.inl hlast
  · right
    have hn : ∃ k, Active p i k ∧ p j < p k := by
      by_contra he
      apply hlast
      refine ⟨hj,fun k hk => ?_⟩
      by_contra hle
      exact he ⟨k,hk,lt_of_not_ge hle⟩
    obtain ⟨k,hk,hjk⟩ := hn
    obtain ⟨l,hl⟩ := next_exists p i j k hk hjk
    exact ⟨l,next_sound p i j l hj hl⟩

end GridHardness.SatColumnCoverage
