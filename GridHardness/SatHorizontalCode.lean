/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatHorizontalDrawing
public import GridHardness.SatClauseConnectionCode

/-!
# SAT Horizontal Code

Polynomial enumeration of the two directed horizontal connector families.
Records contain crossing-cell addresses and a direction tag. They identify
actual graph edges. `SatHorizontalDrawingCode` also computes their endpoint
labels and lattice coordinates.
-/

@[expose] public section

namespace GridHardness.SatHorizontalCode
open CliffordComplexity PlanarSatAssembly SatCrossingConnectionCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev RecordTy := Ty.pair ConnectionTy .bool
abbrev RecordsTy := Ty.list RecordTy

def records : Code SatTy RecordsTy :=
  .comp (.pair SatClauseConnectionCode.horizontal (.const (.list .bool) [false,true])) Code.cross

attribute [local irreducible] SatClauseConnectionCode.horizontal

theorem records_eval (x : SatTy.denote) :
    records.eval x = (SatClauseConnectionCode.horizontal.eval x).product [false,true] := by
  rw [records]
  rfl

def encode {N : Nat} {p : Equiv.Perm (Fin N)} (e : SatHorizontalDrawing.Edge p) :
    RecordTy.denote :=
  (((e.1.val.1.val,e.1.val.2.2.val),(e.1.val.2.1.val,e.1.val.2.2.val)),e.2)

theorem encode_injective {N : Nat} (p : Equiv.Perm (Fin N)) :
    Function.Injective (encode (p := p)) := by
  intro e f h
  have hi := congrArg (fun z : RecordTy.denote => z.1.1.1) h
  have hk := congrArg (fun z : RecordTy.denote => z.1.2.1) h
  have hj := congrArg (fun z : RecordTy.denote => z.1.1.2) h
  have hb := congrArg (fun z : RecordTy.denote => z.2) h
  exact Prod.ext (Subtype.ext (Prod.ext (Fin.ext hi)
    (Prod.ext (Fin.ext hk) (Fin.ext hj)))) hb

theorem encoded_edge_mem (x : SatTy.denote)
    (e : SatHorizontalDrawing.Edge (SatClauseOrder.permutation (finiteFormula x))) :
    encode e ∈ records.eval x := by
  rw [records_eval]
  apply List.mem_product.mpr
  refine ⟨?_,?_⟩
  · exact (SatClauseConnectionCode.horizontal_correct x e.1.val.1 e.1.val.2.1 e.1.val.2.2).mpr
      e.1.property
  · cases e.2 <;> simp

/-- No malformed or extra record is emitted, and every horizontal drawing
edge is emitted. The statement quantifies over arbitrary encoded records. -/
theorem records_correct (x : SatTy.denote) (r : RecordTy.denote) :
    r ∈ records.eval x ↔
      ∃ e : SatHorizontalDrawing.Edge (SatClauseOrder.permutation (finiteFormula x)),
        encode e = r := by
  constructor
  · rcases r with ⟨⟨⟨i,j⟩,⟨k,l⟩⟩,b⟩
    intro h
    rw [records_eval] at h
    have hh := (List.mem_product.mp h).1
    have heval : SatClauseConnectionCode.horizontal.eval x =
        connections.eval (SatClauseOrderCode.crossings.eval x) := by
      rw [SatClauseConnectionCode.horizontal]
      rfl
    rw [heval] at hh
    have hm := (mem_connections (SatClauseOrderCode.crossings.eval x) (i,j) (k,l)).mp hh
    have he : j = l := hm.2.2.1
    subst l
    obtain ⟨hi,hj⟩ := SatClauseOrderCode.crossing_bounds x (i,j) hm.1
    have hk := (SatClauseOrderCode.crossing_bounds x (k,j) hm.2.1).1
    rw [← heval] at hh
    have hc := (SatClauseConnectionCode.horizontal_correct x ⟨i,hi⟩ ⟨k,hk⟩ ⟨j,hj⟩).mp hh
    exact ⟨(⟨(⟨i,hi⟩,⟨k,hk⟩,⟨j,hj⟩),hc⟩,b),rfl⟩
  · rintro ⟨e,rfl⟩
    exact encoded_edge_mem x e

theorem records_nodup (x : SatTy.denote) : (records.eval x).Nodup := by
  rw [records_eval]
  exact (SatClauseConnectionCode.horizontal_nodup x).product (by decide)

theorem records_length (x : SatTy.denote) :
    (records.eval x).length = 2*(SatClauseConnectionCode.horizontal.eval x).length := by
  have h := List.length_product (SatClauseConnectionCode.horizontal.eval x) [false,true]
  rw [records_eval]
  change (List.product (SatClauseConnectionCode.horizontal.eval x) [false,true]).length =
    (SatClauseConnectionCode.horizontal.eval x).length*2 at h
  omega

theorem records_length_le (x : SatTy.denote) :
    (records.eval x).length ≤ 18*x.length*x.length := by
  have h := SatClauseConnectionCode.horizontal_length_le x
  rw [records_length]
  nlinarith

/-- Every emitted record names an actual final-graph arc, with the
source/target convention of the geometric route. -/
theorem emitted_arc (x : SatTy.denote) (r : RecordTy.denote) (hr : r ∈ records.eval x) :
    ∃ e : SatHorizontalDrawing.Edge (SatClauseOrder.permutation (finiteFormula x)),
      encode e = r ∧
      (SatClauseOrder.graph (finiteFormula x)).adj
        (SatHorizontalDrawing.source (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) e)
        (SatHorizontalDrawing.target (finiteFormula x) (SatClauseOrder.permutation (finiteFormula x)) e) := by
  obtain ⟨e,he⟩ := (records_correct x r).mp hr
  exact ⟨e,he,SatHorizontalDrawing.edge_is_arc _ _ e⟩

end GridHardness.SatHorizontalCode
