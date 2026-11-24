/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseWireLattice

/-!
# SAT Row Coverage

Every active crossing has either a preceding/following active crossing
in its horizontal row, or is the actual first/last request of that row.
-/

public section

namespace GridHardness.SatRowCoverage
open SatCrossingRouting SatCrossingHorizontal
set_option autoImplicit false

variable {N : Nat} (p : Equiv.Perm (Fin N))

theorem first_or_previous (i j : Fin N) (hi : Active p i j) :
    SatClauseWireLattice.firstRequest? p j = some i ∨
      ∃ k, ConsecutiveColumns p k i j := by
  classical
  by_cases h : ∃ k, Active p k j ∧ k < i
  · let s := Finset.univ.filter (fun k => Active p k j ∧ k < i)
    have hs : s.Nonempty := by
      obtain ⟨k,hk⟩ := h
      exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩⟩
    let k := s.max' hs
    have hk : Active p k j ∧ k < i := (Finset.mem_filter.mp (s.max'_mem hs)).2
    refine Or.inr ⟨k,hk.1,hi,hk.2,?_⟩
    intro a ha hka
    by_contra hia
    have ham : a ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,lt_of_not_ge hia⟩
    exact (not_le_of_gt hka) (s.le_max' a ham)
  · apply Or.inl
    apply (SatClauseWireLattice.firstRequest_correct p i j).mpr
    exact ⟨hi,fun k hk => le_of_not_gt (fun hki => h ⟨k,hk,hki⟩)⟩

theorem last_or_next (i j : Fin N) (hi : Active p i j) :
    SatCrossingRetirement.Catalogue.lastRequest? p j = some i ∨
      ∃ k, ConsecutiveColumns p i k j := by
  classical
  by_cases h : ∃ k, Active p k j ∧ i < k
  · let s := Finset.univ.filter (fun k => Active p k j ∧ i < k)
    have hs : s.Nonempty := by
      obtain ⟨k,hk⟩ := h
      exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk⟩⟩
    let k := s.min' hs
    have hk : Active p k j ∧ i < k := (Finset.mem_filter.mp (s.min'_mem hs)).2
    exact Or.inr ⟨k,hi,hk.1,hk.2,fun a ha hia =>
      s.min'_le a (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,hia⟩)⟩
  · apply Or.inl
    apply (SatCrossingRetirement.Catalogue.lastRequest_correct p i j).mpr
    exact ⟨hi,fun k hk => le_of_not_gt (fun hik => h ⟨k,hk,hik⟩)⟩

theorem first_none_iff_last_none (j : Fin N) :
    SatClauseWireLattice.firstRequest? p j = none ↔
      SatCrossingRetirement.Catalogue.lastRequest? p j = none := by
  rw [SatClauseWireLattice.firstRequest_none,SatCrossingRetirement.Catalogue.lastRequest_none]

end GridHardness.SatRowCoverage
