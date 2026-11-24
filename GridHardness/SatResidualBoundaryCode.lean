/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatRetiredDrawingCode
public import GridHardness.SatClauseBoundaryCode
public import GridHardness.SatClauseInverseCode

/-!
# SAT Residual Boundary Code

Complete enumeration of the residual portions: empty crossing columns,
and the upper and lower extrema of nonempty columns.
-/

@[expose] public section

namespace GridHardness.SatResidualBoundaryCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatCrossingRetirement SatRetirementGeometryCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000

abbrev Cell (x : SatTy.denote) (b : Bool) :=
  {c : Fin (3*x.length)×Fin (3*x.length) //
    if b then Segments.LastInColumn (perm x) c.1 c.2 else Segments.FirstInColumn (perm x) c.1 c.2}

abbrev Empty (x : SatTy.denote) := {i : Fin (3*x.length) // Segments.EmptyColumn (perm x) i}

def encodeCell {x : SatTy.denote} {b : Bool} (c : Cell x b) : Nat×Nat := ((perm x c.val.2).val,c.val.1.val)

theorem boundary_correct (x : SatTy.denote) (b : Bool) (i j : Fin (3 *x.length)) :
    ((perm x j).val,i.val)∈(SatClauseBoundaryCode.vertical b).eval x ↔
      if b then Segments.LastInColumn (perm x) i j else Segments.FirstInColumn (perm x) i j := by
  rw [SatClauseBoundaryCode.vertical_correct]
  cases b <;> rfl

theorem boundary_bounds (x : SatTy.denote) (b : Bool) (c : Nat ×Nat)
    (hc : c ∈(SatClauseBoundaryCode.vertical b).eval x) : c.1<3*x.length ∧ c.2<3*x.length := by
  have hm := ((SatCrossingExtremaCode.mem_extrema b _ _).mp hc).1
  obtain ⟨hi,j,hj,he⟩ := (SatClauseConnectionCode.mem_verticalCells x c.1 c.2).mp hm
  exact ⟨he ▸ (perm x j).isLt,hi⟩

def cellListEquiv (x : SatTy.denote) (b : Bool) :
    {c : Nat×Nat // c∈(SatClauseBoundaryCode.vertical b).eval x} ≃ Cell x b where
  toFun c :=
    let hb := boundary_bounds x b c.val c.property
    let i : Fin (3*x.length) := ⟨c.val.2,hb.2⟩
    let j := (perm x).symm ⟨c.val.1,hb.1⟩
    ⟨(i,j),(boundary_correct x b i j).mp (by simpa only [j,Equiv.apply_symm_apply] using c.property)⟩
  invFun c := ⟨encodeCell c,(boundary_correct x b c.val.1 c.val.2).mpr c.property⟩
  left_inv c := by apply Subtype.ext; simp [encodeCell,Equiv.apply_symm_apply]
  right_inv c := by apply Subtype.ext; simp [encodeCell,Equiv.symm_apply_apply]

def cells (x : SatTy.denote) (b : Bool) : List (Cell x b) :=
  ((SatClauseBoundaryCode.vertical b).eval x).attach.map (cellListEquiv x b)

theorem cells_encoded (x : SatTy.denote) (b : Bool) :
    (cells x b).map encodeCell=(SatClauseBoundaryCode.vertical b).eval x := by
  simp only [cells,List.map_map]
  have he : (fun c : {c : Nat×Nat // c∈(SatClauseBoundaryCode.vertical b).eval x} =>
      encodeCell (cellListEquiv x b c))=Subtype.val := by
    funext c
    change (encodeCell ((cellListEquiv x b).toFun c))=c.val
    simp [cellListEquiv,encodeCell,Equiv.apply_symm_apply]
  simp only [Function.comp_def]
  rw [he]
  simpa only [id_eq,List.map_id] using
    (List.attach_map_val (l:=(SatClauseBoundaryCode.vertical b).eval x) (f:=id))

theorem cells_complete (x : SatTy.denote) (b : Bool) (c : Cell x b) : c∈cells x b :=
  List.mem_map.mpr ⟨(cellListEquiv x b).symm c,List.mem_attach _ _,(cellListEquiv x b).apply_symm_apply c⟩

def decodeCell : Code (.pair SatTy SatCrossingCode.PairTy) SatCrossingCode.PairTy :=
  .pair (.comp .snd .snd) (.comp (.pair .fst (.comp .snd .fst)) SatClauseInverseCode.code)

theorem decodeCell_eval (x : SatTy.denote) (b : Bool) (c : Cell x b) :
    decodeCell.eval (x,encodeCell c)=(c.val.1.val,c.val.2.val) := by
  change (c.val.1.val,SatClauseInverseCode.code.eval (x,(perm x c.val.2).val))=_
  rw [SatClauseInverseCode.code_eval]

def emptyTest : Code SatRetiredDrawingCode.RowTy .bool :=
  Code.isNil (.comp (.pair (.comp .fst SatClauseConnectionCode.verticalCells) .snd)
    (SatCrossingExtremaCode.atGroup false))

theorem emptyTest_eval (x : SatTy.denote) (i : Fin (3 *x.length)) :
    emptyTest.eval (x,i.val)=true ↔ Segments.EmptyColumn (perm x) i := by
  rw [emptyTest,isNil_eval_true]
  exact SatClauseBoundaryCode.vertical_boundary_empty false x i

def emptyRows : Code SatTy (.list .nat) :=
  .comp (.pair .id SatRetiredDrawingCode.rows) (Code.filterEnv emptyTest)

theorem mem_emptyRows (x : SatTy.denote) (i : Nat) : i∈emptyRows.eval x ↔
    ∃h : i<3*x.length, Segments.EmptyColumn (perm x) ⟨i,h⟩ := by
  change i∈(Code.filterEnv emptyTest).eval (x,SatRetiredDrawingCode.rows.eval x) ↔ _
  rw [filterEnv_eval,SatRetiredDrawingCode.rows_eval]
  simp only [List.mem_filter,List.mem_map,List.mem_finRange,true_and]
  constructor
  · rintro ⟨⟨j,rfl⟩,hj⟩
    exact ⟨j.isLt,(emptyTest_eval x j).mp hj⟩
  · rintro ⟨hi,he⟩
    exact ⟨⟨⟨i,hi⟩,rfl⟩,(emptyTest_eval x ⟨i,hi⟩).mpr he⟩

def emptyListEquiv (x : SatTy.denote) : {i : Nat // i∈emptyRows.eval x} ≃ Empty x where
  toFun i := ⟨⟨i.val,((mem_emptyRows x i.val).mp i.property).choose⟩,
    ((mem_emptyRows x i.val).mp i.property).choose_spec⟩
  invFun i := ⟨i.val.val,(mem_emptyRows x i.val.val).mpr ⟨i.val.isLt,i.property⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def empties (x : SatTy.denote) : List (Empty x) :=
  (emptyRows.eval x).attach.map (emptyListEquiv x)

theorem empties_encoded (x : SatTy.denote) :
    (empties x).map (fun i => i.val.val)=emptyRows.eval x := by
  simp only [empties,List.map_map]
  change ((emptyRows.eval x).attach.map Subtype.val)=_
  simpa only [id_eq,List.map_id] using (List.attach_map_val (l:=emptyRows.eval x) (f:=id))

theorem empties_complete (x : SatTy.denote) (i : Empty x) : i∈empties x :=
  List.mem_map.mpr ⟨(emptyListEquiv x).symm i,List.mem_attach _ _,(emptyListEquiv x).apply_symm_apply i⟩

/-- Boundary enumeration contains neither duplicates nor extraneous cells. -/
theorem cells_nodup (x : SatTy.denote) (b : Bool) : (cells x b).Nodup := by
  apply List.Nodup.of_map (f:=encodeCell)
  rw [cells_encoded]
  exact SatClauseBoundaryCode.vertical_nodup b x

theorem cells_length_le (x : SatTy.denote) (b : Bool) : (cells x b).length≤3*x.length := by
  have he := congrArg List.length (cells_encoded x b)
  simp only [List.length_map] at he
  rw [he]
  exact SatClauseBoundaryCode.vertical_length_le b x

theorem emptyRows_nodup (x : SatTy.denote) : (emptyRows.eval x).Nodup := by
  change ((Code.filterEnv emptyTest).eval (x,SatRetiredDrawingCode.rows.eval x)).Nodup
  rw [filterEnv_eval,SatRetiredDrawingCode.rows_eval]
  exact ((List.nodup_finRange _).map Fin.val_injective).filter _

theorem emptyRows_length_le (x : SatTy.denote) : (emptyRows.eval x).length≤3*x.length := by
  change ((Code.filterEnv emptyTest).eval (x,SatRetiredDrawingCode.rows.eval x)).length≤_
  rw [filterEnv_eval]
  calc
    _ ≤ (SatRetiredDrawingCode.rows.eval x).length := List.length_filter_le _ _
    _ = 3*x.length := by rw [SatRetiredDrawingCode.rows_eval,List.length_map,List.length_finRange]

theorem empties_nodup (x : SatTy.denote) : (empties x).Nodup := by
  apply List.Nodup.of_map (f:=fun i => i.val.val)
  rw [empties_encoded]
  exact emptyRows_nodup x

theorem empties_length_le (x : SatTy.denote) : (empties x).length≤3*x.length := by
  have he := congrArg List.length (empties_encoded x)
  simp only [List.length_map] at he
  rw [he]
  exact emptyRows_length_le x

end GridHardness.SatResidualBoundaryCode
