/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingBoundaryCode
public import GridHardness.SatCrossingRetirementRouting

/-!
# SAT Crossing Retirement Catalogue

The retirement placement uses the last request actually executed by the
ascending sweep. Its finite search and the polynomial boundary compiler
select the same cell, including the no-crossing case.
-/

@[expose] public section

namespace GridHardness.SatCrossingRetirement.Catalogue
open CorrectedSatInterval SatCrossingRouting
set_option autoImplicit false

variable {n : Nat} (p : Equiv.Perm (Fin n))

def lastRequest? (j : Fin n) : Option (Fin n) :=
  if hn : requests (permutationHeight p) j.val ≠ [] then
    some ⟨(requests (permutationHeight p) j.val).getLast hn,
      ((mem_requests _ _ _).mp (List.getLast_mem hn)).1.trans j.isLt⟩
  else none

theorem lastRequest_val (j : Fin n) :
    (lastRequest? p j).map Fin.val = (requests (permutationHeight p) j.val).getLast? := by
  unfold lastRequest?
  split
  · rename_i hn
    exact (List.getLast?_eq_some_getLast hn).symm
  · rename_i hn
    have h : requests (permutationHeight p) j.val=[] := by simpa using hn
    simp [h]

theorem lastRequest_sound (i j : Fin n) (hi : lastRequest? p j =some i) :
    Active p i j ∧ ∀ k, Active p k j → k ≤ i := by
  have hval := lastRequest_val p j
  rw [hi] at hval
  have hlast : (requests (permutationHeight p) j.val).getLast?=some i.val := hval.symm
  have hmem := List.mem_of_getLast? hlast
  refine ⟨(SatCrossingHorizontal.request_iff_active p i j).mp hmem,?_⟩
  intro k hk
  have hkm := (SatCrossingHorizontal.request_iff_active p k j).mpr hk
  have hpair : (requests (permutationHeight p) j.val).Pairwise (· ≤ ·) :=
    (requests_increasing _ _).imp Nat.le_of_lt
  have hb := hpair.rel_getLast hkm
  rw [List.getLast_of_getLast?_eq_some hlast] at hb
  exact hb

theorem lastRequest_correct (i j : Fin n) : lastRequest? p j=some i ↔
    Active p i j ∧ ∀ k, Active p k j → k ≤ i := by
  constructor
  · exact lastRequest_sound p i j
  · rintro ⟨hi,hmax⟩
    have hn : requests (permutationHeight p) j.val≠[] :=
      List.ne_nil_of_mem ((SatCrossingHorizontal.request_iff_active p i j).mpr hi)
    have hex : ∃ k, lastRequest? p j=some k := by simp [lastRequest?,hn]
    obtain ⟨k,hk⟩ := hex
    obtain ⟨hkactive,hkmax⟩ := lastRequest_sound p k j hk
    have he : k=i := le_antisymm (hmax k hkactive) (hkmax i hi)
    simpa only [he] using hk

theorem lastRequest_none (j : Fin n) : lastRequest? p j=none ↔ ∀ i, ¬Active p i j := by
  constructor
  · intro hn i hi
    have he := lastRequest_val p j
    rw [hn] at he
    have hnil := List.getLast?_eq_none_iff.mp he.symm
    have hmem := (SatCrossingHorizontal.request_iff_active p i j).mpr hi
    rw [hnil] at hmem
    contradiction
  · intro h
    cases he : lastRequest? p j with
    | none => rfl
    | some i => exact False.elim (h i (lastRequest_sound p i j he).1)

theorem last_before (j : Fin n) : Placement.LastBefore (lastRequest? p j) j := by
  intro i hi
  exact (lastRequest_sound p i j hi).1.1

/-- The computed retirement column discharges all side conditions of the
concrete bend construction; no placement promise is supplied by a caller. -/
theorem placement_route_endpoints (j : Fin n) (e : Edge) :
    (Placement.edgeRoute p (lastRequest? p j) j e).head? =
      some (Placement.point p (lastRequest? p j) j (XorGadget.arc (edgeArc e)).1) ∧
    (Placement.edgeRoute p (lastRequest? p j) j e).getLast? =
      some (Placement.point p (lastRequest? p j) j (XorGadget.arc (edgeArc e)).2) :=
  Placement.edgeRoute_endpoints p _ j (last_before p j) e

theorem compiled_last_correct (x : CliffordComplexity.SatTy.denote)
    (i j : Fin (3 *x.length)) :
    (i.val,j.val)∈(SatCrossingBoundaryCode.horizontal true).eval x ↔
      lastRequest? (SatWireLayout.permutation (finiteFormula x)) j=some i := by
  rw [SatCrossingBoundaryCode.horizontal_correct, lastRequest_correct]
  rfl

theorem compiled_empty_correct (x : CliffordComplexity.SatTy.denote)
    (j : Fin (3 *x.length)) :
    (SatCrossingExtremaCode.atGroup true).eval (SatCrossingCode.crossings.eval x,j.val)=[] ↔
      lastRequest? (SatWireLayout.permutation (finiteFormula x)) j=none := by
  rw [SatCrossingBoundaryCode.horizontal_boundary_empty, lastRequest_none]

end GridHardness.SatCrossingRetirement.Catalogue
