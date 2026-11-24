/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseWireCode
public import GridHardness.SatCrossingTraceCode
public import GridHardness.SatAffineRangeCode
public import GridHardness.BoundedRangeCode
public import GridHardness.GridFrameCode
public import GridHardness.LatticeRouteOrientationCode

/-!
# SAT Clause Link Geometry Code

Complete clause-to-wire paths, including first-crossing selection and
the uncrossed-wire case. All range fuel is generated from the source formula.
-/

@[expose] public section

namespace GridHardness.SatClauseLinkGeometryCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open SatClauseWireLattice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] SatCrossingTraceCode.rankValue

abbrev RowTy := SatCrossingTraceCode.RowTy
abbrev perm (x : SatTy.denote) := SatClauseOrder.permutation (finiteFormula x)

def lengthFrom : Code SatCrossingCode.PairListTy .nat :=
  .branch (Code.isNil .id) (.const .nat 65)
    (Code.mul (.const .nat 512) (Code.add
      (.comp (.pair .id (.const .nat 0)) (lookupNat SatCrossingCode.PairTy .fst)) (.const .nat 1)))

theorem lengthFrom_nil : lengthFrom.eval []=65 := rfl
theorem lengthFrom_singleton (i j : Nat) : lengthFrom.eval [(i,j)]=512*(i+1) := by
  change 512*((lookupNat SatCrossingCode.PairTy .fst).eval ([(i,j)],0)+1)=_
  rw [lookupNat_eval _ _ _ _ (by simp)]
  rfl

def count : Code RowTy .nat := .comp SatClauseWireCode.firstAt lengthFrom

theorem count_eval (x : SatTy.denote) (j : Fin (3 *x.length)) :
    count.eval (x,j.val)=SatClauseWireLattice.length (perm x) j+1 := by
  change lengthFrom.eval (SatClauseWireCode.firstAt.eval (x,j.val))=_
  rw [SatClauseWireCode.firstAt_correct]
  have hl := length_cast (perm x) j
  change lengthFrom.eval ((firstRequest? (perm x) j).toList.map (fun i => (i.val,j.val)))=_
  generalize hn : SatClauseWireLattice.length (perm x) j = n at hl ⊢
  cases hf : firstRequest? (perm x) j with
  | none =>
    simp only [Option.toList_none,List.map_nil]
    rw [lengthFrom_nil]
    simp only [finishX,hf] at hl
    have hn64 : n = 64 := Int.ofNat_inj.mp (by simpa using hl)
    rw [hn64]
  | some i =>
    simp only [Option.toList_some,List.map_cons,List.map_nil]
    rw [lengthFrom_singleton]
    simp only [finishX,hf,PermutationWireLayout.low] at hl
    have hi : (512*(i.val+1):Nat) = n+1 := by omega
    exact hi

def heightCode (b : Bool) : Code RowTy SignedTy :=
  .comp (.pair (Code.add
    (Code.mul (.const .nat 512)
      (Code.add (Code.add (Code.mul (.const .nat 3) (.comp .fst .listLen)) (.const .nat 2))
        SatCrossingTraceCode.rankValue)) (.const .nat (if b then 0 else 4)))
    (.const .nat (if b then 4 else 0))) normalize

theorem heightCode_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) :
    (heightCode b).eval (x,j.val)=encodeInt (height (perm x) j b) := by
  change normalize.eval (512*(3*x.length+2+SatCrossingTraceCode.rankValue.eval (x,j.val))+
    (if b then 0 else 4),if b then 4 else 0)=_
  rw [SatCrossingTraceCode.rankValue_eval,normalize_eval]
  congr 1
  cases b <;> simp [integer,height,PermutationWireLayout.high] <;> ring

def point : Code (.pair SignedTy .nat) PointTy :=
  .pair (.comp (.pair .snd (.const .nat 64)) normalize) .fst

theorem point_eval (y : Int) (k : Nat) :
    point.eval (encodeInt y,k)=encodePoint (-64+(k:Int),y) := by
  change (normalize.eval (k,64),encodeInt y)=_
  rw [normalize_eval]
  change (encodeInt ((k:Int)-64),encodeInt y)=_
  congr 2 <;> ring

def indices : Code RowTy (.list .nat) :=
  .comp (.pair (.comp .fst (SatAffineRangeCode.padding 1536 0)) count) (BoundedRangeCode.code .nat)

theorem indices_eval (x : SatTy.denote) (j : Fin (3 *x.length)) :
    indices.eval (x,j.val)=List.range (SatClauseWireLattice.length (perm x) j+1) := by
  change (BoundedRangeCode.code .nat).eval ((SatAffineRangeCode.padding 1536 0).eval x,
    count.eval (x,j.val))=_
  rw [count_eval]
  apply BoundedRangeCode.code_eval_of_le
  rw [SatAffineRangeCode.padding_length]
  have h := (route_length_bound (perm x) j false).2
  rw [route_length] at h
  omega

def segmentCode (b : Bool) : Code RowTy CycleInputTy :=
  .comp (.pair (heightCode b) indices) (.listMapEnv point)

theorem segmentCode_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) :
    (segmentCode b).eval (x,j.val)=
      (segment (height (perm x) j b) (SatClauseWireLattice.length (perm x) j)).map encodePoint := by
  change (indices.eval (x,j.val)).map (fun k => point.eval ((heightCode b).eval (x,j.val),k))=_
  rw [indices_eval,heightCode_eval]
  simp only [SatClauseWireLattice.segment,List.map_map]
  exact List.map_congr_left (fun k _ => point_eval _ k)

def code (b : Bool) : Code RowTy CycleInputTy :=
  .comp (.pair (segmentCode b) (.const .bool b)) (LatticeRouteCoreCode.orientCode PointTy)

theorem code_eval (x : SatTy.denote) (j : Fin (3 *x.length)) (b : Bool) :
    (code b).eval (x,j.val)=(route (perm x) j b).map encodePoint := by
  change (LatticeRouteCoreCode.orientCode PointTy).eval ((segmentCode b).eval (x,j.val),b)=_
  rw [segmentCode_eval,LatticeRouteCoreCode.orientCode_eval]
  cases b <;> simp [route,List.map_reverse]

end GridHardness.SatClauseLinkGeometryCode
