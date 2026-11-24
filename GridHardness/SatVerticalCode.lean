/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVerticalArcs
public import GridHardness.SatClauseConnectionCode

/-!
# SAT Vertical Code

Exact syntax-driven enumeration of the four directed vertical connectors.
Cell records retain permutation heights, which determine their rows uniquely.
-/

@[expose] public section

namespace GridHardness.SatVerticalCode
open CliffordComplexity PlanarSatAssembly SatCrossingConnectionCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev RecordTy := Ty.pair ConnectionTy .nat
abbrev RecordsTy := Ty.list RecordTy
abbrev Edge (x : SatTy.denote) := SatVerticalDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))

def records : Code SatTy RecordsTy :=
  .comp (.pair SatClauseConnectionCode.vertical (.const (.list .nat) (List.range 4))) Code.cross

def encode (x : SatTy.denote) (e : Edge x) : RecordTy.denote :=
  (((((SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.1).val,e.1.val.1.val),
    (((SatClauseOrder.permutation (finiteFormula x)) e.1.val.2.2).val,e.1.val.1.val)),e.2.val)

attribute [local irreducible] SatClauseConnectionCode.vertical

theorem records_eval (x : SatTy.denote) :
    records.eval x=(SatClauseConnectionCode.vertical.eval x).product (List.range 4) := by
  rw [records]
  rfl

theorem encoded_edge_mem (x : SatTy.denote) (e : Edge x) : encode x e∈records.eval x := by
  rw [records_eval]
  exact List.mem_product.mpr
    ⟨(SatClauseConnectionCode.vertical_correct x e.1.val.1 e.1.val.2.1 e.1.val.2.2).mpr e.1.property,
      List.mem_range.mpr e.2.isLt⟩

theorem records_correct (x : SatTy.denote) (r : RecordTy.denote) :
    r∈records.eval x ↔ ∃ e : Edge x, encode x e=r := by
  constructor
  · rcases r with ⟨⟨⟨a,i⟩,⟨b,l⟩⟩,r⟩
    intro hm
    rw [records_eval] at hm
    obtain ⟨hc,hr⟩ := List.mem_product.mp hm
    have heval : SatClauseConnectionCode.vertical.eval x =
        connections.eval (SatClauseConnectionCode.verticalCells.eval x) := by
      rw [SatClauseConnectionCode.vertical]
      rfl
    rw [heval] at hc
    have hs := (mem_connections (SatClauseConnectionCode.verticalCells.eval x) (a,i) (b,l)).mp hc
    have hil : i=l := hs.2.2.1
    subst l
    obtain ⟨hi,j,hj,ha⟩ := (SatClauseConnectionCode.mem_verticalCells x a i).mp hs.1
    obtain ⟨_,k,hk,hb⟩ := (SatClauseConnectionCode.mem_verticalCells x b i).mp hs.2.1
    subst a b
    rw [← heval] at hc
    have he := (SatClauseConnectionCode.vertical_correct x ⟨i,hi⟩ j k).mp hc
    exact ⟨(⟨(⟨i,hi⟩,j,k),he⟩,⟨r,List.mem_range.mp hr⟩),rfl⟩
  · rintro ⟨e,rfl⟩
    exact encoded_edge_mem x e

theorem records_length_le (x : SatTy.denote) :
    (records.eval x).length≤36*x.length*x.length := by
  have hp := List.length_product (SatClauseConnectionCode.vertical.eval x) (List.range 4)
  change (List.product (SatClauseConnectionCode.vertical.eval x) (List.range 4)).length = _ at hp
  rw [List.length_range] at hp
  rw [records_eval,hp]
  have h := SatClauseConnectionCode.vertical_length_le x
  nlinarith

end GridHardness.SatVerticalCode
