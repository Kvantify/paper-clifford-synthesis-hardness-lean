/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseOrderCode
public import GridHardness.SatCrossingVerticalCode

/-!
# SAT Clause Connection Code

Instantiate the bounded horizontal and vertical connection searches
with the reversed clause-block permutation. Vertical cell names explicitly
use permutation heights, not row identifiers.
-/

@[expose] public section

namespace GridHardness.SatClauseConnectionCode
open CliffordComplexity PlanarSatAssembly SatClauseOrderCode SatCrossingConnectionCode
open SatCrossingCode (PairListTy)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

def horizontal : Code SatTy ConnectionsTy := .comp crossings connections

theorem horizontal_correct (x : SatTy.denote) (i k j : Fin (3 *x.length)) :
    ((i.val,j.val),(k.val,j.val))∈horizontal.eval x ↔
      SatCrossingHorizontal.ConsecutiveColumns
        (SatClauseOrder.permutation (finiteFormula x)) i k j := by
  change _∈connections.eval (crossings.eval x) ↔ _
  rw [mem_connections,crossing_cell_iff,crossing_cell_iff]
  constructor
  · rintro ⟨hi,hk,_,hik,h⟩
    refine ⟨hi,hk,hik,?_⟩
    intro a ha hia
    exact h (a.val,j.val) ((crossing_cell_iff x a j).mpr ha) rfl hia
  · rintro ⟨hi,hk,hik,h⟩
    refine ⟨hi,hk,rfl,hik,?_⟩
    rintro ⟨a,b⟩ hc he hia
    dsimp at he hia ⊢
    subst b
    obtain ⟨ha,_⟩ := crossing_bounds x (a,j.val) hc
    exact h ⟨a,ha⟩ ((crossing_cell_iff x ⟨a,ha⟩ j).mp hc) hia

theorem horizontal_nodup (x : SatTy.denote) : (horizontal.eval x).Nodup :=
  connections_nodup _ (crossings_nodup x)

theorem horizontal_length_le (x : SatTy.denote) :
    (horizontal.eval x).length≤9*x.length*x.length :=
  (connections_length_le_cells _ (crossings_nodup x)).trans (crossings_length_le x)

/-- A vertical crossing is encoded by `(p(row),column)`. -/
def verticalCells : Code SatTy PairListTy := .comp indexed verticalInversions

theorem mem_verticalCells (x : SatTy.denote) (h i : Nat) :
    (h,i)∈verticalCells.eval x ↔ ∃ (hi : i<3*x.length) (j : Fin (3*x.length)),
      SatCrossingRouting.Active (SatClauseOrder.permutation (finiteFormula x)) ⟨i,hi⟩ j ∧
        h=(SatClauseOrder.permutation (finiteFormula x) j).val := by
  change (h,i)∈verticalInversions.eval (indexed.eval x) ↔ _
  rw [mem_verticalInversions]
  constructor
  · rintro ⟨a,l,ha,hb,hil,hha⟩
    obtain ⟨hi,rfl⟩ := (mem_indexed x a i).mp ha
    obtain ⟨hl,rfl⟩ := (mem_indexed x h l).mp hb
    exact ⟨hi,⟨l,hl⟩,⟨hil,hha⟩,rfl⟩
  · rintro ⟨hi,j,⟨hij,hji⟩,rfl⟩
    exact ⟨(SatClauseOrder.permutation (finiteFormula x) ⟨i,hi⟩).val,j.val,
      (mem_indexed x _ i).mpr ⟨hi,rfl⟩,
      (mem_indexed x _ j.val).mpr ⟨j.isLt,rfl⟩,hij,hji⟩

theorem vertical_cell_iff (x : SatTy.denote) (i j : Fin (3 *x.length)) :
    ((SatClauseOrder.permutation (finiteFormula x) j).val,i.val)∈verticalCells.eval x ↔
      SatCrossingRouting.Active (SatClauseOrder.permutation (finiteFormula x)) i j := by
  rw [mem_verticalCells]
  constructor
  · rintro ⟨hi,k,hk,he⟩
    have hkj : k=j := (SatClauseOrder.permutation (finiteFormula x)).injective
      (Fin.ext he.symm)
    subst k
    exact hk
  · intro h
    exact ⟨i.isLt,j,h,rfl⟩

theorem verticalCells_length_le (x : SatTy.denote) :
    (verticalCells.eval x).length≤9*x.length*x.length := by
  have h := verticalInversions_length_le (indexed.eval x)
  have hi : (indexed.eval x).length=3*x.length := by
    change (permutation.eval x).zipIdx.length=_
    rw [List.length_zipIdx,permutation_length]
  rw [hi] at h
  change (verticalInversions.eval (indexed.eval x)).length≤_
  nlinarith

theorem verticalCells_nodup (x : SatTy.denote) : (verticalCells.eval x).Nodup := by
  apply verticalInversions_nodup
  · change ((permutation.eval x).zipIdx.map Prod.fst).Nodup
    rw [List.zipIdx_map_fst]
    exact permutation_nodup x
  · change ((permutation.eval x).zipIdx.map Prod.snd).Nodup
    rw [List.zipIdx_map_snd,← List.range_eq_range']
    exact List.nodup_range

def vertical : Code SatTy ConnectionsTy := .comp verticalCells connections

theorem vertical_correct (x : SatTy.denote) (i j k : Fin (3 *x.length)) :
    (((SatClauseOrder.permutation (finiteFormula x) j).val,i.val),
      ((SatClauseOrder.permutation (finiteFormula x) k).val,i.val))∈vertical.eval x ↔
      SatCrossingRouting.Consecutive (SatClauseOrder.permutation (finiteFormula x)) i j k := by
  change _∈connections.eval (verticalCells.eval x) ↔ _
  rw [mem_connections,vertical_cell_iff,vertical_cell_iff]
  constructor
  · rintro ⟨hj,hk,_,hjk,h⟩
    refine ⟨hj,hk,hjk,?_⟩
    intro a ha hja
    exact h ((SatClauseOrder.permutation (finiteFormula x) a).val,i.val)
      ((vertical_cell_iff x i a).mpr ha) rfl hja
  · rintro ⟨hj,hk,hjk,h⟩
    refine ⟨hj,hk,rfl,hjk,?_⟩
    rintro ⟨a,b⟩ hc he hja
    dsimp at he hja ⊢
    subst b
    obtain ⟨hi,l,hl,hal⟩ := (mem_verticalCells x a i.val).mp hc
    subst a
    exact h l hl hja

theorem vertical_length_le (x : SatTy.denote) :
    (vertical.eval x).length≤9*x.length*x.length :=
  (connections_length_le_cells _ (verticalCells_nodup x)).trans (verticalCells_length_le x)

theorem vertical_nodup (x : SatTy.denote) : (vertical.eval x).Nodup :=
  connections_nodup _ (verticalCells_nodup x)

end GridHardness.SatClauseConnectionCode
