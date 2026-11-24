/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatClauseBodyCatalogue
public import GridHardness.SatAffineRangeCode

/-!
# SAT Variable Position Code

Source-driven occurrence counts, variable-block prefixes, and exact
coordinates for all variable-body vertices.
-/

@[expose] public section

namespace GridHardness.SatVariablePositionCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 800000

abbrev InputTy := Ty.pair SatTy .nat

def count : Code InputTy .nat := .comp PlanarSatCode.occurrencesFor .listLen

theorem count_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    count.eval (x,v.val)=SatVariableOrder.count (finiteFormula x) v := by
  change (PlanarSatCode.occurrencesFor.eval (x,v.val)).length=_
  rw [PlanarSatCode.occurrencesFor_eval,List.length_map]
  rfl

def lower : Code InputTy (.list .nat) :=
  .comp (.pair .snd (.comp .fst PlanarSatCode.variableIndices))
    (Code.filterEnv (.comp (.pair .snd .fst) .natLt))

theorem lower_eval (x : SatTy.denote) (v : Nat) :
    lower.eval (x,v)=((List.finRange ((vsOf x).length+1)).filter
      (fun w => decide (w.val<v))).map Fin.val := by
  change (Code.filterEnv (.comp (.pair .snd .fst) .natLt)).eval
    (v,PlanarSatCode.variableIndices.eval x)=_
  rw [filterEnv_eval]
  rw [PlanarSatCode.variableIndices_finite,List.filter_map]
  simp only [Function.comp_def,Code.eval]
  congr 1
  exact List.filter_congr (fun w _ => CliffordComplexity.natLt_eval w.val v)

def prefixCode : Code InputTy .nat :=
  .comp (.pair .fst lower) (.comp (.listMapEnv count) .listSum)

theorem prefixCode_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    prefixCode.eval (x,v.val)=SatVariableOrder.prefix (finiteFormula x) v := by
  change ((lower.eval (x,v.val)).map (fun w => count.eval (x,w))).sum=_
  rw [lower_eval,List.map_map,SatVariableOrder.prefix_sum_lower]
  congr 1
  exact List.map_congr_left (fun w _ => count_eval x w)

def xCode : Code InputTy SignedTy :=
  .comp (.pair (Code.add (Code.mul (.const .nat 1536) (.comp .fst .listLen))
    (.const .nat 641)) (.const .nat 0)) normalize

def entryY : Code InputTy SignedTy :=
  .comp (.pair (Code.add (Code.mul (.const .nat 512) prefixCode) (.const .nat 128))
    (.const .nat 0)) normalize

def exitY : Code InputTy SignedTy :=
  .branch (.comp (.pair count (.const .nat 0)) .natEq)
    (.comp (.pair (Code.add (Code.mul (.const .nat 512) prefixCode) (.const .nat 192))
      (.const .nat 0)) normalize)
    (.comp (.pair (Code.add (Code.mul (.const .nat 512) (Code.add prefixCode count))
      (.const .nat 64)) (.const .nat 0)) normalize)

def point (b : Bool) : Code InputTy PointTy := .pair xCode (if b then exitY else entryY)

theorem xCode_eval (x : SatTy.denote) (v : Nat) :
    xCode.eval (x,v)=encodeInt (SatVariableLattice.wireX (3*x.length)+64) := by
  change normalize.eval (1536*x.length+641,0)=_
  rw [normalize_eval]
  congr 1
  simp only [integer,SatVariableLattice.wireX,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

theorem entryY_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) :
    entryY.eval (x,v.val)=encodeInt (SatVariableLattice.entryY
      (SatVariableOrder.prefix (finiteFormula x) v)) := by
  change normalize.eval (512*prefixCode.eval (x,v.val)+128,0)=_
  rw [prefixCode_eval,normalize_eval]
  congr 1

theorem point_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) (b : Bool) :
    (point b).eval (x,v.val)=encodePoint (SatVariablePlacement.point (finiteFormula x) v b) := by
  cases b with
  | false =>
    change (xCode.eval (x,v.val),entryY.eval (x,v.val))=_
    rw [xCode_eval,entryY_eval]
    rfl
  | true =>
    change (xCode.eval (x,v.val),exitY.eval (x,v.val))=_
    rw [xCode_eval]
    simp only [exitY,Code.add,Code.mul,Code.eval]
    simp only [count_eval x v,prefixCode_eval x v,decide_eq_true_eq]
    split_ifs with h
    · rw [normalize_eval]
      simp only [SatVariablePlacement.point,ite_eq_left h]
      apply Prod.ext rfl
      congr 1
    · rw [normalize_eval]
      simp only [SatVariablePlacement.point,ite_eq_right h]
      rfl

end GridHardness.SatVariablePositionCode
