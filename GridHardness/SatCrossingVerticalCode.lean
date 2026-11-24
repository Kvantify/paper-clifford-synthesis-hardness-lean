/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingConnectionCode

/-!
# SAT Crossing Vertical Code

The vertical connection compiler uses permutation heights as its ordered
coordinate. Thus the same bounded consecutive-pair search also supplies the
premise of the four directed vertical routing certificates.
-/

@[expose] public section

namespace GridHardness.SatCrossingConnectionCode
open CliffordComplexity SatCrossingCode PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 400000

/-- Retain the second height and first column of each inversion. -/
def verticalInversions : Code PairListTy PairListTy :=
  .comp (.pair .id .id) (.comp Code.cross
    (.comp (.listFilter inversionTest)
      (.listMap (.pair (.comp .snd .fst) (.comp .fst .snd)))))

theorem verticalInversions_eval (l : List (Nat × Nat)) :
    verticalInversions.eval l =
      ((l.product l).filter inversionTest.eval).map (fun p => (p.2.1,p.1.2)) := by
  change ((((l.map (fun a => l.map (fun b => (a,b)))).flatten).filter
    inversionTest.eval).map (fun p => (p.2.1,p.1.2))) = _
  rw [← List.flatMap_def]
  rfl

theorem mem_verticalInversions (l : List (Nat × Nat)) (h i : Nat) :
    (h,i) ∈ verticalInversions.eval l ↔
      ∃ a j : Nat, (a,i) ∈ l ∧ (h,j) ∈ l ∧ i<j ∧ h<a := by
  rw [verticalInversions_eval]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨⟨a,k⟩,⟨b,j⟩⟩,⟨hp,ht⟩,he⟩
    obtain ⟨ha,hb⟩ := List.mem_product.mp hp
    obtain ⟨hkj,hba⟩ := (inversionTest_eval (a,k) (b,j)).mp ht
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨a,j,ha,hb,hkj,hba⟩
  · rintro ⟨a,j,ha,hb,hij,hha⟩
    exact ⟨((a,i),(h,j)),⟨List.mem_product.mpr ⟨ha,hb⟩,
      (inversionTest_eval _ _).mpr ⟨hij,hha⟩⟩,rfl⟩

theorem verticalInversions_nodup (l : List (Nat × Nat))
    (hf : (l.map Prod.fst).Nodup) (hs : (l.map Prod.snd).Nodup) :
    (verticalInversions.eval l).Nodup := by
  rw [verticalInversions_eval]
  have hl : l.Nodup := hs.of_map Prod.snd
  apply List.Nodup.map_on _ ((hl.product hl).filter _)
  intro a ha b hb he
  have ha' := List.mem_product.mp (List.mem_of_mem_filter ha)
  have hb' := List.mem_product.mp (List.mem_of_mem_filter hb)
  have hh := Prod.mk.inj he
  exact Prod.ext
    (List.inj_on_of_nodup_map (f := fun p : Nat × Nat => p.2) hs ha'.1 hb'.1 hh.2)
    (List.inj_on_of_nodup_map (f := fun p : Nat × Nat => p.1) hf ha'.2 hb'.2 hh.1)

theorem verticalInversions_length_le (l : List (Nat × Nat)) :
    (verticalInversions.eval l).length ≤ l.length*l.length := by
  rw [verticalInversions_eval, List.length_map, ← List.length_product]
  exact List.length_filter_le _ _

/-- Encode a crossing by `(height, column)` instead of `(column, row)`. -/
def verticalCells : Code SatTy PairListTy := .comp indexed verticalInversions

theorem mem_verticalCells (x : SatTy.denote) (h i : Nat) :
    (h,i) ∈ verticalCells.eval x ↔ ∃ (hi : i<3*x.length) (j : Fin (3*x.length)),
      SatCrossingRouting.Active (SatWireLayout.permutation (finiteFormula x)) ⟨i,hi⟩ j ∧
        h=(SatWireLayout.permutation (finiteFormula x) j).val := by
  change (h,i) ∈ verticalInversions.eval (indexed.eval x) ↔ _
  rw [mem_verticalInversions]
  constructor
  · rintro ⟨a,l,ha,hb,hil,hha⟩
    obtain ⟨hi,rfl⟩ := (mem_indexed x a i).mp ha
    obtain ⟨hl,rfl⟩ := (mem_indexed x h l).mp hb
    exact ⟨hi,⟨l,hl⟩,⟨hil,hha⟩,rfl⟩
  · rintro ⟨hi,j,⟨hij,hji⟩,rfl⟩
    exact ⟨(SatWireLayout.permutation (finiteFormula x) ⟨i,hi⟩).val,j.val,
      (mem_indexed x _ i).mpr ⟨hi,rfl⟩,
      (mem_indexed x _ j.val).mpr ⟨j.isLt,rfl⟩,hij,hji⟩

theorem vertical_cell_iff (x : SatTy.denote) (i j : Fin (3 *x.length)) :
    ((SatWireLayout.permutation (finiteFormula x) j).val,i.val) ∈ verticalCells.eval x ↔
      SatCrossingRouting.Active (SatWireLayout.permutation (finiteFormula x)) i j := by
  rw [mem_verticalCells]
  constructor
  · rintro ⟨hi,k,hk,he⟩
    have hkj : k=j := (SatWireLayout.permutation (finiteFormula x)).injective
      (Fin.ext he.symm)
    subst k
    exact hk
  · intro h
    exact ⟨i.isLt,j,h,rfl⟩

theorem verticalCells_length_le (x : SatTy.denote) :
    (verticalCells.eval x).length ≤ 9*x.length*x.length := by
  have h := verticalInversions_length_le (indexed.eval x)
  have hi : (indexed.eval x).length = 3*x.length := by
    change (permutation.eval x).zipIdx.length = _
    rw [List.length_zipIdx, permutation_length]
  rw [hi] at h
  change (verticalInversions.eval (indexed.eval x)).length ≤ _
  nlinarith

theorem verticalCells_nodup (x : SatTy.denote) : (verticalCells.eval x).Nodup := by
  apply verticalInversions_nodup
  · change ((permutation.eval x).zipIdx.map Prod.fst).Nodup
    rw [List.zipIdx_map_fst, permutation_eval]
    exact (SatWireLayout.variableOrder_nodup (finiteFormula x)).map
      (fun a b he => (SatWireLayout.clauseRank x.length).injective (Fin.ext he))
  · change ((permutation.eval x).zipIdx.map Prod.snd).Nodup
    rw [List.zipIdx_map_snd, ← List.range_eq_range']
    exact List.nodup_range

/-- The first components name heights; the common second component names
the vertical column. Heights uniquely identify rows in the permutation. -/
def vertical : Code SatTy ConnectionsTy := .comp verticalCells connections

theorem vertical_correct (x : SatTy.denote) (i j k : Fin (3 *x.length)) :
    (((SatWireLayout.permutation (finiteFormula x) j).val,i.val),
      ((SatWireLayout.permutation (finiteFormula x) k).val,i.val)) ∈ vertical.eval x ↔
      SatCrossingRouting.Consecutive (SatWireLayout.permutation (finiteFormula x)) i j k := by
  change _ ∈ connections.eval (verticalCells.eval x) ↔ _
  rw [mem_connections, vertical_cell_iff, vertical_cell_iff]
  constructor
  · rintro ⟨hj,hk,_,hjk,h⟩
    refine ⟨hj,hk,hjk,?_⟩
    intro a ha hja
    exact h ((SatWireLayout.permutation (finiteFormula x) a).val,i.val)
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
    (vertical.eval x).length ≤ 9*x.length*x.length :=
  (connections_length_le_cells _ (verticalCells_nodup x)).trans (verticalCells_length_le x)

theorem vertical_nodup (x : SatTy.denote) : (vertical.eval x).Nodup :=
  connections_nodup _ (verticalCells_nodup x)

end GridHardness.SatCrossingConnectionCode
