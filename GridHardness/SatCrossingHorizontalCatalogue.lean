/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.CorrectedSatIntervalCatalogue
public import GridHardness.SatCrossingHorizontalRouting

/-!
# SAT Crossing Horizontal Catalogue

Select consecutive horizontal crossing columns from the actual permutation.
The geometric consecutiveness premise follows from this finite search and
agrees with the request set executed by the two-sided SAT sweep.
-/

@[expose] public section

namespace GridHardness.SatCrossingHorizontal
open SatCrossingRouting CorrectedSatInterval
set_option autoImplicit false

variable {n : Nat} (p : Equiv.Perm (Fin n))

theorem request_iff_active (i j : Fin n) :
    i.val ∈ requests (permutationHeight p) j.val ↔ Active p i j := by
  rw [mem_requests, permutationHeight_apply, permutationHeight_apply]
  simp [Active]

def nextColumns (i j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => Active p k j ∧ i<k)

def nextColumn? (i j : Fin n) : Option (Fin n) :=
  if h : (nextColumns p i j).Nonempty then some ((nextColumns p i j).min' h) else none

theorem nextColumn_sound (i k j : Fin n) (hi : Active p i j)
    (hk : nextColumn? p i j = some k) : ConsecutiveColumns p i k j := by
  unfold nextColumn? at hk
  split at hk
  next h =>
    have he := Option.some.inj hk
    subst k
    have hm := (Finset.mem_filter.mp (Finset.min'_mem (nextColumns p i j) h)).2
    refine ⟨hi,hm.1,hm.2,?_⟩
    intro a ha hia
    apply Finset.min'_le
    simp [nextColumns,ha,hia]
  next h => contradiction

theorem nextColumn_exists (i j k : Fin n) (hk : Active p k j) (hik : i <k) :
    ∃ a, nextColumn? p i j = some a := by
  have hn : (nextColumns p i j).Nonempty := by
    refine ⟨k,?_⟩
    simp [nextColumns,hk,hik]
  simp [nextColumn?,hn]

theorem nextColumn_complete (i k j : Fin n) (hc : ConsecutiveColumns p i k j) :
    nextColumn? p i j = some k := by
  obtain ⟨a,ha⟩ := nextColumn_exists p i j k hc.2.1 hc.2.2.1
  have hca := nextColumn_sound p i a j hc.1 ha
  have hak : a≤k := hca.2.2.2 k hc.2.1 hc.2.2.1
  have hka : k≤a := hc.2.2.2 a hca.2.1 hca.2.2.1
  simpa [le_antisymm hak hka] using ha

theorem nextColumn_correct (i k j : Fin n) (hi : Active p i j) :
    nextColumn? p i j = some k ↔ ConsecutiveColumns p i k j :=
  ⟨nextColumn_sound p i k j hi, nextColumn_complete p i k j⟩

/-- Starting at any actual sweep request, the computed successor supplies the
entire combinatorial premise of the horizontal routing certificates. -/
theorem nextColumn_from_request (i k j : Fin n)
    (hi : i.val ∈ requests (permutationHeight p) j.val)
    (hk : nextColumn? p i j = some k) : ConsecutiveColumns p i k j :=
  nextColumn_sound p i k j ((request_iff_active p i j).mp hi) hk

end GridHardness.SatCrossingHorizontal
