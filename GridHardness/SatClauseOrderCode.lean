/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseOrder
public import GridHardness.SatCrossingCode

/-!
# SAT Clause Order Code

Polynomial list programs for the reversed clause-block order. All loops
range over explicit input-derived lists. The emitted inversion cells agree
with both the geometric permutation and the actual insertion sweep.
-/

@[expose] public section

namespace GridHardness.SatClauseOrderCode
open CliffordComplexity PlanarSatAssembly
open SatCrossingCode (NatListTy PairTy PairListTy)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

/-- Original clause/slot identifiers in variable-chain order. -/
def occurrences : Code SatTy (.list PlanarSatCode.OccTy) :=
  .comp (.pair .id PlanarSatCode.variableIndices)
    (.comp (.listMapEnv PlanarSatCode.occurrencesFor) .listJoin)

theorem occurrences_eval (x : SatTy.denote) : occurrences.eval x=
    (SatWireLayout.variableOrder (finiteFormula x)).map (fun o => (o.1.val,o.2.val)) := by
  change ((PlanarSatCode.variableIndices.eval x).map
    (fun v => PlanarSatCode.occurrencesFor.eval (x,v))).flatten=_
  rw [PlanarSatCode.variableIndices_finite]
  simp only [List.map_map,Function.comp_def,← List.flatMap_def]
  rw [SatWireLayout.variableOrder,List.map_flatMap]
  apply List.flatMap_congr
  intro v _
  exact PlanarSatCode.occurrencesFor_eval x v

/-- Reverse clause blocks while retaining the three literal slots. -/
def occurrenceNumber : Code (.pair SatTy PlanarSatCode.OccTy) .nat :=
  Code.add
    (Code.mul (.comp (.pair (.comp .fst .listLen)
      (Code.add (.comp .snd .fst) (.const .nat 1))) .natSub) (.const .nat 3))
    (.comp .snd .snd)

theorem occurrenceNumber_eval (x : SatTy.denote) (c j : Nat) :
    occurrenceNumber.eval (x,(c,j))=(x.length-(c+1))*3+j := rfl

theorem occurrenceNumber_rank (x : SatTy.denote) (o : Occurrence x.length) :
    occurrenceNumber.eval (x,(o.1.val,o.2.val))=
      (SatClauseOrder.clauseOrder x.length o).val := by
  rw [occurrenceNumber_eval,SatClauseOrder.clauseOrder_val]
  rfl

/-- The values of the reversed-block occurrence permutation, in domain order. -/
def permutation : Code SatTy NatListTy :=
  .comp (.pair .id occurrences) (.listMapEnv occurrenceNumber)

theorem permutation_eval (x : SatTy.denote) : permutation.eval x=
    (SatWireLayout.variableOrder (finiteFormula x)).map
      (fun o => (SatClauseOrder.clauseOrder x.length o).val) := by
  change (occurrences.eval x).map (fun o => occurrenceNumber.eval (x,o))=_
  rw [occurrences_eval,List.map_map]
  apply List.map_congr_left
  intro o _
  exact occurrenceNumber_rank x o

theorem permutation_length (x : SatTy.denote) :
    (permutation.eval x).length=3*x.length := by
  rw [permutation_eval,List.length_map,SatWireLayout.variableOrder_length]

theorem permutation_get (x : SatTy.denote) (i : Fin (3 *x.length)) :
    (permutation.eval x)[i.val]'(by rw [permutation_length]; exact i.isLt)=
      (SatClauseOrder.permutation (finiteFormula x) i).val := by
  simp only [permutation_eval,List.getElem_map]
  rfl

theorem permutation_nodup (x : SatTy.denote) : (permutation.eval x).Nodup := by
  rw [permutation_eval]
  exact (SatWireLayout.variableOrder_nodup (finiteFormula x)).map
    (fun a b he => (SatClauseOrder.clauseOrder x.length).injective (Fin.ext he))

def indexed : Code SatTy PairListTy := .comp permutation .listEnum

theorem mem_indexed (x : SatTy.denote) (v i : Nat) :
    (v,i)∈indexed.eval x ↔ ∃ hi : i<3*x.length,
      v=(SatClauseOrder.permutation (finiteFormula x) ⟨i,hi⟩).val := by
  change (v,i)∈(permutation.eval x).zipIdx ↔ _
  rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨hi,he⟩
    have hi' : i<3*x.length := by rw [← permutation_length x]; exact hi
    exact ⟨hi',he.symm.trans (permutation_get x ⟨i,hi'⟩)⟩
  · rintro ⟨hi,he⟩
    refine ⟨by rw [permutation_length]; exact hi,?_⟩
    exact (permutation_get x ⟨i,hi⟩).trans he.symm

def crossings : Code SatTy PairListTy := .comp indexed SatCrossingCode.inversions

theorem mem_crossings (x : SatTy.denote) (i j : Nat) :
    (i,j)∈crossings.eval x ↔
      ∃ (hi : i<3*x.length) (hj : j<3*x.length),
        i<j ∧ SatClauseOrder.permutation (finiteFormula x) ⟨j,hj⟩<
          SatClauseOrder.permutation (finiteFormula x) ⟨i,hi⟩ := by
  change (i,j)∈SatCrossingCode.inversions.eval (indexed.eval x) ↔ _
  rw [SatCrossingCode.mem_inversions]
  constructor
  · rintro ⟨a,b,ha,hb,hij,hba⟩
    obtain ⟨hi,rfl⟩ := (mem_indexed x a i).mp ha
    obtain ⟨hj,rfl⟩ := (mem_indexed x b j).mp hb
    exact ⟨hi,hj,hij,hba⟩
  · rintro ⟨hi,hj,hij,hji⟩
    exact ⟨(SatClauseOrder.permutation (finiteFormula x) ⟨i,hi⟩).val,
      (SatClauseOrder.permutation (finiteFormula x) ⟨j,hj⟩).val,
      (mem_indexed x _ i).mpr ⟨hi,rfl⟩,
      (mem_indexed x _ j).mpr ⟨hj,rfl⟩,hij,hji⟩

theorem crossing_cell_iff (x : SatTy.denote) (i j : Fin (3 *x.length)) :
    (i.val,j.val)∈crossings.eval x ↔
      i<j ∧ SatClauseOrder.permutation (finiteFormula x) j<
        SatClauseOrder.permutation (finiteFormula x) i := by
  rw [mem_crossings]
  constructor
  · rintro ⟨_,_,hij,hji⟩
    exact ⟨hij,hji⟩
  · rintro ⟨hij,hji⟩
    exact ⟨i.isLt,j.isLt,hij,hji⟩

theorem crossings_nodup (x : SatTy.denote) : (crossings.eval x).Nodup := by
  apply SatCrossingCode.inversions_nodup
  change ((permutation.eval x).zipIdx.map Prod.snd).Nodup
  rw [List.zipIdx_map_snd,← List.range_eq_range']
  exact List.nodup_range

theorem crossings_length_le (x : SatTy.denote) :
    (crossings.eval x).length≤9*x.length*x.length := by
  have h := SatCrossingCode.inversions_length_le (indexed.eval x)
  have hi : (indexed.eval x).length=3*x.length := by
    change (permutation.eval x).zipIdx.length=_
    rw [List.length_zipIdx,permutation_length]
  rw [hi] at h
  change (SatCrossingCode.inversions.eval (indexed.eval x)).length≤_
  nlinarith

theorem crossing_bounds (x : SatTy.denote) (c : Nat ×Nat) (hc : c ∈crossings.eval x) :
    c.1<3*x.length ∧ c.2<3*x.length := by
  obtain ⟨hi,hj,_,_⟩ := (mem_crossings x c.1 c.2).mp hc
  exact ⟨hi,hj⟩

def cellListEquiv (x : SatTy.denote) :
    {c : Nat×Nat // c∈crossings.eval x} ≃
      WireCrossingSchedule.Cell (SatClauseOrder.permutation (finiteFormula x)) where
  toFun c := ⟨(⟨c.val.1,(crossing_bounds x c.val c.property).1⟩,
      ⟨c.val.2,(crossing_bounds x c.val c.property).2⟩),
    (crossing_cell_iff x _ _).mp c.property⟩
  invFun c := ⟨(c.val.1.val,c.val.2.val),(crossing_cell_iff x _ _).mpr c.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def cellEquiv (x : SatTy.denote) : Fin (crossings.eval x).length ≃
    WireCrossingSchedule.Cell (SatClauseOrder.permutation (finiteFormula x)) :=
  (List.Nodup.getEquiv _ (crossings_nodup x)).trans (cellListEquiv x)

theorem crossings_length (x : SatTy.denote) : (crossings.eval x).length=
    Fintype.card (WireCrossingSchedule.Cell (SatClauseOrder.permutation (finiteFormula x))) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (cellEquiv x)

open CorrectedSatInterval in
theorem trace_mem_iff (x : SatTy.denote) (c : Nat ×Nat) :
    c∈trace (permutationHeight (SatClauseOrder.permutation (finiteFormula x))) (3*x.length) 0 ↔
      c∈crossings.eval x := by
  constructor
  · intro hc
    have hb := (mem_trace _ _ _ c).mp hc
    have hi : c.1<3*x.length := by omega
    have hj : c.2<3*x.length := by omega
    exact (crossing_cell_iff x ⟨c.1,hi⟩ ⟨c.2,hj⟩).mpr
      ((PermutationGraph.covers_inversion _ ⟨c.1,hi⟩ ⟨c.2,hj⟩).mp hc)
  · intro hc
    obtain ⟨hi,hj⟩ := crossing_bounds x c hc
    exact (PermutationGraph.covers_inversion _ ⟨c.1,hi⟩ ⟨c.2,hj⟩).mpr
      ((crossing_cell_iff x ⟨c.1,hi⟩ ⟨c.2,hj⟩).mp hc)

open CorrectedSatInterval in
theorem trace_perm (x : SatTy.denote) :
    (trace (permutationHeight (SatClauseOrder.permutation (finiteFormula x))) (3*x.length) 0).Perm
      (crossings.eval x) :=
  (List.perm_ext_iff_of_nodup (trace_nodup _ _ _) (crossings_nodup x)).mpr (trace_mem_iff x)

open CorrectedSatInterval in
theorem actual_move_count (x : SatTy.denote) :
    moveCount (permutationHeight (SatClauseOrder.permutation (finiteFormula x))) (3*x.length) 0=
      (crossings.eval x).length := by
  rw [← trace_length]
  exact (trace_perm x).length_eq

end GridHardness.SatClauseOrderCode
