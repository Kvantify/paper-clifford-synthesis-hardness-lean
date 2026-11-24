/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseConnectionCode
public import GridHardness.SatCrossingBoundaryCode

/-!
# SAT Clause Boundary Code

First and last crossing records for the reversed clause-block order,
including empty horizontal and vertical wires. The constant-size boundary
record shape and generic extrema searches are shared with the generic
catalogue compiler; all cells here use the reversed clause-block permutation.
-/

@[expose] public section

namespace GridHardness.SatClauseBoundaryCode
open CliffordComplexity PlanarSatAssembly SatClauseOrderCode SatCrossingExtremaCode
open SatCrossingCode (PairListTy)
open SatCrossingBoundaryCode (BoundaryTy BoundariesTy boundaryAt boundaryAt_eval)
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

def horizontal (last : Bool) : Code SatTy PairListTy := .comp crossings (extrema last)
def vertical (last : Bool) : Code SatTy PairListTy :=
  .comp SatClauseConnectionCode.verticalCells (extrema last)

theorem horizontal_correct (last : Bool) (x : SatTy.denote) (i j : Fin (3 *x.length)) :
    (i.val,j.val)∈(horizontal last).eval x ↔
      SatCrossingRouting.Active (SatClauseOrder.permutation (finiteFormula x)) i j ∧
        ∀ a, SatCrossingRouting.Active (SatClauseOrder.permutation (finiteFormula x)) a j →
          if last then a ≤ i else i ≤ a := by
  change _∈(extrema last).eval (crossings.eval x) ↔ _
  rw [mem_extrema,crossing_cell_iff]
  constructor
  · rintro ⟨hi,h⟩
    refine ⟨hi,?_⟩
    intro a ha
    have hh := h (a.val,j.val) ((crossing_cell_iff x a j).mpr ha) rfl
    cases last <;> exact hh
  · rintro ⟨hi,h⟩
    refine ⟨hi,?_⟩
    rintro ⟨a,b⟩ hc he
    change j.val=b at he
    subst b
    have ha := (crossing_bounds x (a,j.val) hc).1
    have hh := h ⟨a,ha⟩ ((crossing_cell_iff x ⟨a,ha⟩ j).mp hc)
    cases last <;> exact hh

theorem vertical_correct (last : Bool) (x : SatTy.denote) (i j : Fin (3 *x.length)) :
    ((SatClauseOrder.permutation (finiteFormula x) j).val,i.val)∈(vertical last).eval x ↔
      SatCrossingRouting.Active (SatClauseOrder.permutation (finiteFormula x)) i j ∧
        ∀ k, SatCrossingRouting.Active (SatClauseOrder.permutation (finiteFormula x)) i k →
          if last then SatClauseOrder.permutation (finiteFormula x) k≤
            SatClauseOrder.permutation (finiteFormula x) j
          else SatClauseOrder.permutation (finiteFormula x) j≤
            SatClauseOrder.permutation (finiteFormula x) k := by
  change _∈(extrema last).eval (SatClauseConnectionCode.verticalCells.eval x) ↔ _
  rw [mem_extrema,SatClauseConnectionCode.vertical_cell_iff]
  constructor
  · rintro ⟨hi,h⟩
    refine ⟨hi,?_⟩
    intro k hk
    have hh := h ((SatClauseOrder.permutation (finiteFormula x) k).val,i.val)
      ((SatClauseConnectionCode.vertical_cell_iff x i k).mpr hk) rfl
    cases last <;> exact hh
  · rintro ⟨hi,h⟩
    refine ⟨hi,?_⟩
    rintro ⟨a,b⟩ hc he
    change i.val=b at he
    subst b
    obtain ⟨_,k,hk,rfl⟩ := (SatClauseConnectionCode.mem_verticalCells x a i.val).mp hc
    have hh := h k hk
    cases last <;> exact hh

theorem horizontal_nodup (last : Bool) (x : SatTy.denote) :
    ((horizontal last).eval x).Nodup := extrema_nodup _ _ (crossings_nodup x)

theorem vertical_nodup (last : Bool) (x : SatTy.denote) :
    ((vertical last).eval x).Nodup :=
  extrema_nodup _ _ (SatClauseConnectionCode.verticalCells_nodup x)

theorem horizontal_length_le (last : Bool) (x : SatTy.denote) :
    ((horizontal last).eval x).length≤3*x.length :=
  extrema_length_le _ _ (crossings_nodup x) _ (fun a ha => (crossing_bounds x a ha).2)

theorem vertical_length_le (last : Bool) (x : SatTy.denote) :
    ((vertical last).eval x).length≤3*x.length := by
  apply extrema_length_le _ _ (SatClauseConnectionCode.verticalCells_nodup x)
  intro a ha
  obtain ⟨hi,_,_,_⟩ := (SatClauseConnectionCode.mem_verticalCells x a.1 a.2).mp ha
  exact hi

def boundaries (cells : Code SatTy PairListTy) : Code SatTy BoundariesTy :=
  .comp (.pair .id (.comp permutation Code.indices)) (.listMapEnv (boundaryAt cells))

attribute [local irreducible] permutation boundaryAt

theorem boundaries_eval (cells : Code SatTy PairListTy) (x : SatTy.denote) :
    (boundaries cells).eval x=(List.range (3*x.length)).map
      (fun j => (boundaryAt cells).eval (x,j)) := by
  change ((Code.indices (τ:=.nat)).eval (permutation.eval x)).map
    (fun j => (boundaryAt cells).eval (x,j))=_
  rw [indices_eval,permutation_length]

theorem boundaries_length (cells : Code SatTy PairListTy) (x : SatTy.denote) :
    ((boundaries cells).eval x).length=3*x.length := by
  rw [boundaries_eval,List.length_map,List.length_range]

theorem boundaries_get (cells : Code SatTy PairListTy) (x : SatTy.denote)
    (j : Fin (3 *x.length)) :
    ((boundaries cells).eval x)[j.val]'(by rw [boundaries_length]; exact j.isLt)=
      (j.val,((atGroup false).eval (cells.eval x,j.val),
        (atGroup true).eval (cells.eval x,j.val))) := by
  have hj : j.val < ((boundaries cells).eval x).length := by
    rw [boundaries_length]
    exact j.isLt
  have h := congrArg (fun l : BoundariesTy.denote => l[j.val]?) (boundaries_eval cells x)
  simp only [List.getElem?_eq_getElem hj, List.getElem?_map, List.getElem?_range j.isLt,
    Option.map_some, Option.some.injEq] at h
  exact h.trans (boundaryAt_eval cells x j.val)

def horizontalBoundaries : Code SatTy BoundariesTy := boundaries crossings
def verticalBoundaries : Code SatTy BoundariesTy := boundaries SatClauseConnectionCode.verticalCells

theorem horizontal_boundary_empty (last : Bool) (x : SatTy.denote) (j : Fin (3 *x.length)) :
    (atGroup last).eval (crossings.eval x,j.val)=[] ↔
      ∀ i, ¬SatCrossingRouting.Active (SatClauseOrder.permutation (finiteFormula x)) i j := by
  rw [atGroup_nil_iff]
  constructor
  · intro h i hi
    exact h (i.val,j.val) ((crossing_cell_iff x i j).mpr hi) rfl
  · rintro h ⟨a,b⟩ hc he
    change b=j.val at he
    subst b
    have ha := (crossing_bounds x (a,j.val) hc).1
    exact h ⟨a,ha⟩ ((crossing_cell_iff x ⟨a,ha⟩ j).mp hc)

theorem vertical_boundary_empty (last : Bool) (x : SatTy.denote) (i : Fin (3 *x.length)) :
    (atGroup last).eval (SatClauseConnectionCode.verticalCells.eval x,i.val)=[] ↔
      ∀ j, ¬SatCrossingRouting.Active (SatClauseOrder.permutation (finiteFormula x)) i j := by
  rw [atGroup_nil_iff]
  constructor
  · intro h j hj
    exact h ((SatClauseOrder.permutation (finiteFormula x) j).val,i.val)
      ((SatClauseConnectionCode.vertical_cell_iff x i j).mpr hj) rfl
  · rintro h ⟨a,b⟩ hc he
    change b=i.val at he
    subst b
    obtain ⟨_,j,hj,_⟩ := (SatClauseConnectionCode.mem_verticalCells x a i.val).mp hc
    exact h j hj

end GridHardness.SatClauseBoundaryCode
