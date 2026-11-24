/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseBoundaryCode
public import GridHardness.SatClauseWireLattice

/-!
# SAT Clause Wire Code

Polynomial-cost selection of the actual clause-link endpoints.
A record is emitted for every occurrence, with either the unique first
crossing or an empty list for an uncrossed wire. This does not compile
the complete graph or its lattice routes.
-/

@[expose] public section

namespace GridHardness.SatClauseWireCode
open CliffordComplexity PlanarSatAssembly
open SatCrossingExtremaCode SatClauseWireLattice
set_option autoImplicit false

abbrev RecordTy : Ty := .pair .nat SatCrossingCode.PairListTy
abbrev RecordsTy : Ty := .list RecordTy

def firstAt : Code (.pair SatTy .nat) SatCrossingCode.PairListTy :=
  .comp (.pair (.comp .fst SatClauseOrderCode.crossings) .snd) (atGroup false)

theorem firstAt_some (x : SatTy.denote) (i j : Fin (3 *x.length)) :
    (i.val,j.val)∈firstAt.eval (x,j.val) ↔
      firstRequest? (SatClauseOrder.permutation (finiteFormula x)) j=some i := by
  change _∈(atGroup false).eval (SatClauseOrderCode.crossings.eval x,j.val) ↔ _
  rw [mem_atGroup]
  change ((i.val,j.val)∈(SatClauseBoundaryCode.horizontal false).eval x ∧ j.val=j.val) ↔ _
  simp only [and_true]
  rw [SatClauseBoundaryCode.horizontal_correct,firstRequest_correct]
  rfl

theorem firstAt_length_le_one (x : SatTy.denote) (j : Nat) :
    (firstAt.eval (x,j)).length≤1 :=
  atGroup_length_le_one false _ (SatClauseOrderCode.crossings_nodup x) j

theorem firstAt_empty (x : SatTy.denote) (j : Fin (3 *x.length)) :
    firstAt.eval (x,j.val)=[] ↔
      firstRequest? (SatClauseOrder.permutation (finiteFormula x)) j=none :=
  (SatClauseBoundaryCode.horizontal_boundary_empty false x j).trans
    (firstRequest_none _ j).symm

theorem firstAt_correct (x : SatTy.denote) (j : Fin (3 *x.length)) :
    firstAt.eval (x,j.val)=
      ((firstRequest? (SatClauseOrder.permutation (finiteFormula x)) j).toList.map
        (fun i => (i.val,j.val))) := by
  cases h : firstRequest? (SatClauseOrder.permutation (finiteFormula x)) j with
  | none => exact (firstAt_empty x j).mpr h
  | some i =>
    have hm := (firstAt_some x i j).mpr h
    have hl := firstAt_length_le_one x j.val
    cases he : firstAt.eval (x,j.val) with
    | nil => simp only [he,List.not_mem_nil] at hm
    | cons a as =>
      have has : as=[] := List.length_eq_zero_iff.mp (by simp only [he,List.length_cons] at hl; omega)
      subst as
      have ha : a=(i.val,j.val) :=
        (by simpa only [he,List.mem_singleton] using hm : (i.val,j.val)=a).symm
      simp only [ha,Option.toList_some,List.map_cons,List.map_nil]

def records : Code SatTy RecordsTy :=
  .comp (.pair .id (.comp SatClauseOrderCode.permutation Code.indices))
    (.listMapEnv (.pair .snd firstAt))

attribute [local irreducible] SatClauseOrderCode.permutation firstAt

theorem records_eval (x : SatTy.denote) :
    records.eval x=(List.range (3*x.length)).map (fun j => (j,firstAt.eval (x,j))) := by
  change ((Code.indices (τ:=.nat)).eval (SatClauseOrderCode.permutation.eval x)).map
    (fun j => (j,firstAt.eval (x,j)))=_
  rw [indices_eval,SatClauseOrderCode.permutation_length]

theorem records_length (x : SatTy.denote) : (records.eval x).length=3*x.length := by
  rw [records_eval,List.length_map,List.length_range]

theorem records_get (x : SatTy.denote) (j : Fin (3 *x.length)) :
    (records.eval x)[j.val]'(by rw [records_length]; exact j.isLt)=
      (j.val,(firstRequest? (SatClauseOrder.permutation (finiteFormula x)) j).toList.map
        (fun i => (i.val,j.val))) := by
  have hj : j.val < (records.eval x).length := by
    rw [records_length]
    exact j.isLt
  have h := congrArg (fun l : RecordsTy.denote => l[j.val]?) (records_eval x)
  simp only [List.getElem?_eq_getElem hj, List.getElem?_map, List.getElem?_range j.isLt,
    Option.map_some, Option.some.injEq] at h
  rw [h, firstAt_correct x j]

theorem records_nodup (x : SatTy.denote) : (records.eval x).Nodup := by
  rw [records_eval]
  apply List.Nodup.map _ List.nodup_range
  intro i j h
  exact congrArg Prod.fst h

end GridHardness.SatClauseWireCode
