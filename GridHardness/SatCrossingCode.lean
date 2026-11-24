/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.XorWireCodeSat
public import GridHardness.SatWireLayout
public import GridHardness.WireCrossingSchedule

/-!
# SAT Crossing Code

A list-bounded program enumerating exactly the inversions of the actual
SAT occurrence permutation. This supplies the crossing catalogue needed by
the graph compiler. It does not assert a drawing of the graph's ports.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

namespace GridHardness.SatCrossingCode
open CliffordComplexity PlanarSatAssembly

abbrev NatListTy := Ty.list .nat
abbrev PairTy := Ty.pair .nat .nat
abbrev PairListTy := Ty.list PairTy

def occurrenceNumber : Code PlanarSatCode.OccTy .nat :=
  Code.add (Code.mul .fst (.const .nat 3)) .snd

/-- Clause-order labels in the exact variable-chain order. -/
def permutation : Code SatTy NatListTy :=
  .comp (.pair .id PlanarSatCode.variableIndices)
    (.comp (.listMapEnv (.comp PlanarSatCode.occurrencesFor
      (.listMap occurrenceNumber))) .listJoin)

theorem permutation_eval (x : SatTy.denote) : permutation.eval x =
    (SatWireLayout.variableOrder (finiteFormula x)).map
      (fun o => (SatWireLayout.clauseRank x.length o).val) := by
  change ((PlanarSatCode.variableIndices.eval x).map (fun v =>
    (PlanarSatCode.occurrencesFor.eval (x,v)).map occurrenceNumber.eval)).flatten = _
  rw [PlanarSatCode.variableIndices_finite]
  simp only [List.map_map, Function.comp_def, ← List.flatMap_def]
  rw [SatWireLayout.variableOrder, List.map_flatMap]
  apply List.flatMap_congr
  intro v _
  rw [PlanarSatCode.occurrencesFor_eval x v, List.map_map]
  apply List.map_congr_left
  intro o _
  rw [SatWireLayout.clauseRank_val]
  rfl

theorem permutation_length (x : SatTy.denote) : (permutation.eval x).length = 3*x.length := by
  rw [permutation_eval, List.length_map, SatWireLayout.variableOrder_length]

theorem permutation_get (x : SatTy.denote) (i : Fin (3 *x.length)) :
    (permutation.eval x)[i.val]'(by rw [permutation_length]; exact i.isLt) =
      (SatWireLayout.permutation (finiteFormula x) i).val := by
  simp only [permutation_eval x, List.getElem_map]
  rfl

def indexed : Code SatTy PairListTy := .comp permutation .listEnum

theorem mem_indexed (x : SatTy.denote) (v i : Nat) :
    (v,i) ∈ indexed.eval x ↔
      ∃ hi : i < 3*x.length,
        v = (SatWireLayout.permutation (finiteFormula x) ⟨i,hi⟩).val := by
  change (v,i) ∈ (permutation.eval x).zipIdx ↔ _
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
  constructor
  · rintro ⟨hi,he⟩
    have hi' : i < 3*x.length := by rw [← permutation_length x]; exact hi
    exact ⟨hi', he.symm.trans (permutation_get x ⟨i,hi'⟩)⟩
  · rintro ⟨hi,he⟩
    refine ⟨by rw [permutation_length x]; exact hi, ?_⟩
    exact (permutation_get x ⟨i,hi⟩).trans he.symm

def inversionTest : Code (.pair PairTy PairTy) .bool :=
  Code.and (Code.lt (.comp .fst .snd) (.comp .snd .snd))
    (Code.lt (.comp .snd .fst) (.comp .fst .fst))

theorem inversionTest_eval (a b : Nat ×Nat) :
    inversionTest.eval (a,b) = true ↔ a.2 < b.2 ∧ b.1 < a.1 := by
  change (Code.natLt.eval (a.2,b.2) && Code.natLt.eval (b.1,a.1)) = true ↔ _
  rw [Bool.and_eq_true, natLt_eval_true, natLt_eval_true]

def inversions : Code PairListTy PairListTy :=
  .comp (.pair .id .id) (.comp Code.cross
    (.comp (.listFilter inversionTest) (.listMap (.pair (.comp .fst .snd) (.comp .snd .snd)))))

theorem mem_inversions (l : List (Nat ×Nat)) (i j : Nat) :
    (i,j) ∈ inversions.eval l ↔
      ∃ a b : Nat, (a,i) ∈ l ∧ (b,j) ∈ l ∧ i < j ∧ b < a := by
  change (i,j) ∈ (((Code.cross (σ := PairTy) (τ := PairTy)).eval
    (l,l)).filter inversionTest.eval).map (fun p => (p.1.2,p.2.2)) ↔ _
  simp only [List.mem_map, List.mem_filter, mem_cross_eval (σ := PairTy) (τ := PairTy)]
  constructor
  · rintro ⟨⟨⟨a,k⟩,⟨b,l⟩⟩,⟨⟨ha,hb⟩,ht⟩,he⟩
    obtain ⟨hkl,hba⟩ := (inversionTest_eval (a,k) (b,l)).mp ht
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨a,b,ha,hb,hkl,hba⟩
  · rintro ⟨a,b,ha,hb,hij,hba⟩
    exact ⟨((a,i),(b,j)),⟨⟨ha,hb⟩,
      (inversionTest_eval (a,i) (b,j)).mpr ⟨hij,hba⟩⟩,rfl⟩

theorem inversions_eval (l : List (Nat ×Nat)) : inversions.eval l =
    ((l.product l).filter inversionTest.eval).map (fun p => (p.1.2,p.2.2)) := by
  change ((((l.map (fun a => l.map (fun b => (a,b)))).flatten).filter
    inversionTest.eval).map (fun p => (p.1.2,p.2.2))) = _
  rw [← List.flatMap_def]
  rfl

theorem inversions_nodup (l : List (Nat ×Nat)) (hn : (l.map Prod.snd).Nodup) :
    (inversions.eval l).Nodup := by
  rw [inversions_eval]
  have hl : l.Nodup := hn.of_map Prod.snd
  apply List.Nodup.map_on _ ((hl.product hl).filter _)
  intro a ha b hb he
  have ha' := List.mem_product.mp (List.mem_of_mem_filter ha)
  have hb' := List.mem_product.mp (List.mem_of_mem_filter hb)
  have hparts := Prod.mk.inj he
  have hefirst : a.1 = b.1 :=
    List.inj_on_of_nodup_map (f := fun p : Nat×Nat => p.2) hn ha'.1 hb'.1 hparts.1
  have hesecond : a.2 = b.2 :=
    List.inj_on_of_nodup_map (f := fun p : Nat×Nat => p.2) hn ha'.2 hb'.2 hparts.2
  exact Prod.ext hefirst hesecond

theorem inversions_length_le (l : List (Nat ×Nat)) :
    (inversions.eval l).length ≤ l.length*l.length := by
  rw [inversions_eval, List.length_map, ← List.length_product]
  exact List.length_filter_le _ _

/-- Every loop ranges over the explicit occurrence list. -/
def crossings : Code SatTy PairListTy := .comp indexed inversions

theorem mem_crossings (x : SatTy.denote) (i j : Nat) :
    (i,j) ∈ crossings.eval x ↔
      ∃ (hi : i < 3*x.length) (hj : j < 3*x.length),
        i < j ∧ SatWireLayout.permutation (finiteFormula x) ⟨j,hj⟩ <
          SatWireLayout.permutation (finiteFormula x) ⟨i,hi⟩ := by
  change (i,j) ∈ inversions.eval (indexed.eval x) ↔ _
  rw [mem_inversions]
  constructor
  · rintro ⟨a,b,ha,hb,hij,hba⟩
    obtain ⟨hi,rfl⟩ := (mem_indexed x a i).mp ha
    obtain ⟨hj,rfl⟩ := (mem_indexed x b j).mp hb
    exact ⟨hi,hj,hij,hba⟩
  · rintro ⟨hi,hj,hij,hji⟩
    let a := (SatWireLayout.permutation (finiteFormula x) ⟨i,hi⟩).val
    let b := (SatWireLayout.permutation (finiteFormula x) ⟨j,hj⟩).val
    exact ⟨a,b,(mem_indexed x a i).mpr ⟨hi,rfl⟩,
      (mem_indexed x b j).mpr ⟨hj,rfl⟩,hij,hji⟩

theorem crossing_cell_iff (x : SatTy.denote) (i j : Fin (3 *x.length)) :
    (i.val,j.val) ∈ crossings.eval x ↔
      i < j ∧ SatWireLayout.permutation (finiteFormula x) j <
        SatWireLayout.permutation (finiteFormula x) i := by
  rw [mem_crossings]
  constructor
  · rintro ⟨_,_,hij,hji⟩
    exact ⟨hij,hji⟩
  · rintro ⟨hij,hji⟩
    exact ⟨i.isLt,j.isLt,hij,hji⟩

theorem crossings_nodup (x : SatTy.denote) : (crossings.eval x).Nodup := by
  apply inversions_nodup
  change ((permutation.eval x).zipIdx.map Prod.snd).Nodup
  rw [List.zipIdx_map_snd, ← List.range_eq_range']
  exact List.nodup_range

theorem crossings_length_le (x : SatTy.denote) :
    (crossings.eval x).length ≤ 9*x.length*x.length := by
  have h := inversions_length_le (indexed.eval x)
  have hi : (indexed.eval x).length = 3*x.length := by
    change (permutation.eval x).zipIdx.length = _
    rw [List.length_zipIdx, permutation_length]
  rw [hi] at h
  change (inversions.eval (indexed.eval x)).length ≤ _
  nlinarith

theorem crossing_bounds (x : SatTy.denote) (p : Nat ×Nat) (hp : p ∈ crossings.eval x) :
    p.1 < 3*x.length ∧ p.2 < 3*x.length := by
  obtain ⟨hi,hj,_,_⟩ := (mem_crossings x p.1 p.2).mp hp
  exact ⟨hi,hj⟩

def cellListEquiv (x : SatTy.denote) :
    {p : Nat×Nat // p ∈ crossings.eval x} ≃
      WireCrossingSchedule.Cell (SatWireLayout.permutation (finiteFormula x)) where
  toFun p := ⟨(⟨p.1.1,(crossing_bounds x p.1 p.2).1⟩,
      ⟨p.1.2,(crossing_bounds x p.1 p.2).2⟩),
    (crossing_cell_iff x _ _).mp p.2⟩
  invFun c := ⟨(c.1.1.val,c.1.2.val), (crossing_cell_iff x _ _).mpr c.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The emitted positions number every scheduled crossing exactly once. -/
def cellEquiv (x : SatTy.denote) : Fin (crossings.eval x).length ≃
    WireCrossingSchedule.Cell (SatWireLayout.permutation (finiteFormula x)) :=
  (List.Nodup.getEquiv _ (crossings_nodup x)).trans (cellListEquiv x)

theorem crossings_length (x : SatTy.denote) : (crossings.eval x).length =
    Fintype.card (WireCrossingSchedule.Cell (SatWireLayout.permutation (finiteFormula x))) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (cellEquiv x)

end GridHardness.SatCrossingCode
