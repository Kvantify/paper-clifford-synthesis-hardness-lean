/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatCrossingTraceCode
public import GridHardness.SatRetiredSideDrawing
public import GridHardness.SatClauseBodyCatalogue

/-!
# SAT Retirement Geometry Code

The two endpoint columns of each retired XOR, computed from SAT syntax.
The last requested crossing is found in the explicit chronological request
list; the empty list selects the clause boundary.
-/

@[expose] public section

namespace GridHardness.SatRetirementGeometryCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open CorrectedSatInterval SatCrossingRetirement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000
attribute [local irreducible] SatCrossingTraceCode.rankValue

abbrev RowTy := SatCrossingTraceCode.RowTy
abbrev perm (x : SatTy.denote) := SatClauseOrder.permutation (finiteFormula x)

def lastValue : Code (.list .nat) .nat :=
  .comp (.pair .id (.comp (.pair .listLen (.const .nat 1)) .natSub)) (lookupNat .nat .id)

theorem lastValue_eval (xs : List Nat) (h : xs ≠[]) : lastValue.eval xs=xs.getLast h := by
  change (lookupNat .nat .id).eval (xs,xs.length-1)=_
  rw [lookupNat_eval .nat .id xs _ (by exact Nat.sub_lt (List.length_pos_iff.mpr h) (by decide))]
  exact (List.getLast_eq_getElem h).symm

def leftList : Code (.list .nat) .nat :=
  .branch (Code.isNil .id) (.const .nat 0)
    (Code.add (Code.mul (.const .nat 512) (Code.add lastValue (.const .nat 1))) (.const .nat 55))

theorem leftList_eval (xs : List Nat) : leftList.eval xs=
    if h : xs=[] then 0 else 512*(xs.getLast h+1)+55 := by
  change (if (Code.isNil (.id : Code (.list .nat) (.list .nat))).eval xs=true then 0
    else 512*(lastValue.eval xs+1)+55)=_
  by_cases h : xs=[]
  · have hb : (Code.isNil (.id : Code (.list .nat) (.list .nat))).eval xs=true :=
      (isNil_eval_true (.id : Code (.list .nat) (.list .nat)) xs).mpr h
    rw [ite_eq_left hb,dite_eq_left h]
  · have hb : ¬(Code.isNil (.id : Code (.list .nat) (.list .nat))).eval xs=true :=
      fun hh => h ((isNil_eval_true (.id : Code (.list .nat) (.list .nat)) xs).mp hh)
    rw [ite_eq_right hb,dite_eq_right h,lastValue_eval _ h]

def leftNat : Code RowTy .nat := .comp SatCrossingTraceCode.rowRequests leftList

theorem leftNat_eval (x : SatTy.denote) (j : Fin (3 *x.length)) :
    (leftNat.eval (x,j.val):Int)=Placement.left (Residual.rowEnd (perm x) j) := by
  change (leftList.eval (SatCrossingTraceCode.rowRequests.eval (x,j.val)):Int)=_
  rw [SatCrossingTraceCode.rowRequests_eval,leftList_eval]
  unfold Residual.rowEnd Catalogue.lastRequest? perm
  by_cases h : requests (permutationHeight (SatClauseOrder.permutation (finiteFormula x))) j.val=[]
  · simp [h,Placement.left]
  · simp only [dite_eq_right h,dite_eq_left h,Placement.left,PermutationWireLayout.low]
    push_cast
    rfl

def rightNat : Code RowTy .nat :=
  Code.add (Code.mul (.const .nat 512)
    (Code.add (Code.mul (.const .nat 3) (.comp .fst .listLen)) (.const .nat 1))) (.const .nat 65)
def lowNat : Code RowTy .nat := Code.mul (.const .nat 512) (Code.add .snd (.const .nat 1))
def highNat : Code RowTy .nat := Code.mul (.const .nat 512)
  (Code.add (Code.add (Code.mul (.const .nat 3) (.comp .fst .listLen)) (.const .nat 2))
    SatCrossingTraceCode.rankValue)

def columnArithmetic (z : Int) : Code (.pair .nat .nat) PointTy :=
  .pair (.comp (.pair .fst (.const .nat 0)) normalize)
    (.comp (.pair (.comp (.pair .snd (.const .nat 0)) normalize)
      (.const SignedTy (encodeInt z))) addSigned)

theorem columnArithmetic_eval (a b : Nat) (z : Int) :
    (columnArithmetic z).eval (a,b)=encodePoint ((a:Int),(b:Int)+z) := by
  change (normalize.eval (a,0),addSigned.eval (normalize.eval (b,0),encodeInt z))=_
  rw [normalize_eval,addSigned_eval,normalize_eval,integer_encodeInt,integer_encodeInt]
  rfl

def columnPoint (b : Bool) (z : Int) : Code RowTy PointTy :=
  .comp (.pair (if b then rightNat else leftNat) (if b then lowNat else highNat)) (columnArithmetic z)

theorem columnPoint_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) (z : Int) :
    (columnPoint b z).eval (x,j.val)=encodePoint
      (if b then (512*((3*x.length:Int)+1)+65,512*PermutationWireLayout.low j+z)
       else (Placement.left (Residual.rowEnd (perm x) j),512*PermutationWireLayout.high (perm x) j+z)) := by
  cases b
  · change (columnArithmetic z).eval (leftNat.eval (x,j.val),highNat.eval (x,j.val))=_
    rw [columnArithmetic_eval,leftNat_eval]
    change encodePoint (_,((512*(3*x.length+2+SatCrossingTraceCode.rankValue.eval (x,j.val))):Nat)+z)=_
    rw [SatCrossingTraceCode.rankValue_eval]; rfl
  · change (columnArithmetic z).eval (512*(3*x.length+1)+65,512*(j.val+1))=_
    rw [columnArithmetic_eval]; rfl

def pointCode (v : Fin 8) : Code RowTy PointTy :=
  columnPoint (decide (v.val<4)) (offset ⟨v.val%4,Nat.mod_lt _ (by decide)⟩)

theorem pointCode_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (v : Fin 8) :
    (pointCode v).eval (x,j.val)=encodePoint (SatRetiredSideDrawing.point (perm x) (j,v)) := by
  obtain ⟨r,rfl|rfl⟩ := vertex_split v
  · have hr := r.isLt
    simp only [pointCode,trueVertex,Nat.mod_eq_of_lt hr,hr,decide_true]
    rw [columnPoint_eval]
    change _=encodePoint (Placement.point (perm x) _ j (trueVertex r))
    rw [Placement.true_coordinates (perm x) (Residual.rowEnd (perm x) j) j (Catalogue.last_before _ _) r]; rfl
  · have hr := r.isLt
    simp only [pointCode,falseVertex,show ¬r.val+4<4 by omega,decide_false,
      Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_eq_of_lt hr]
    rw [columnPoint_eval]
    change _=encodePoint (Placement.point (perm x) _ j (falseVertex r))
    rw [Placement.false_coordinates (perm x) (Residual.rowEnd (perm x) j) j (Catalogue.last_before _ _) r]; rfl

def sideCode (e : Fin 6) : Code RowTy CycleInputTy :=
  PlanarSatCode.table (sidePoints e) (columnPoint (sideTrue e))

theorem sideCode_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (e : Fin 6) :
    (sideCode e).eval (x,j.val)=(SatRetiredSideDrawing.route (perm x) (j,e)).map encodePoint := by
  rw [sideCode,PlanarSatCode.table_eval]
  change _=(((sidePoints e).map (sidePoint _ _ _ e)).map (Placement.frame _ j).map).map encodePoint
  rw [List.map_map,List.map_map]
  apply List.map_congr_left
  intro z _
  rw [columnPoint_eval]
  have hp := Placement.parameters (perm x) (Residual.rowEnd (perm x) j) j (Catalogue.last_before _ _)
  simp only [Function.comp_def,sidePoint]
  cases he : sideTrue e <;> simp only [he,Bool.false_eq_true,ite_false,ite_true]
  all_goals rw [Placement.frame_map]; congr 1; apply Prod.ext <;> dsimp [finish] <;> omega

end GridHardness.SatRetirementGeometryCode
