/-
Copyright (c) 2026 Kvantify. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Søren Fuglede Jørgensen
-/

module

public import CslibFrontier.Init
public import GridHardness.SatVariableBodyCode

/-!
# SAT Variable Chain Route Code

The variable occurrence-chain's three constant-length lattice templates,
indexed by the actual position in that variable's occurrence list.
-/

@[expose] public section

namespace GridHardness.SatVariableChainRouteCode
open CliffordComplexity CliffordSynthesis GridProblems GridProblems.GridCode GridPointCode
open PlanarSatAssembly SatVariablePositionCode
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The proof unfolds nested program combinators to identify the emitted records.
set_option maxHeartbeats 1200000

abbrev LinkTy := Ty.pair SatVariablePositionCode.InputTy .nat
abbrev SampleTy := Ty.pair LinkTy .nat

def literalX : Code SampleTy .nat :=
  Code.add (Code.mul (.const .nat 1536) (.comp (.comp (.comp .fst .fst) .fst) .listLen))
    (.const .nat 577)
def blockStart : Code SampleTy .nat := .comp (.comp .fst .fst) prefixCode
def blockEnd : Code SampleTy .nat := .comp (.comp .fst .fst) (Code.add prefixCode SatVariablePositionCode.count)
def sample : Code SampleTy .nat := .snd
def linkIndex : Code SampleTy .nat := .comp .fst .snd
def signed (a b : Code SampleTy .nat) : Code SampleTy SignedTy := .comp (.pair a b) normalize
def pos (a : Code SampleTy .nat) : Code SampleTy SignedTy := signed a (.const .nat 0)

def entryPoint : Code SampleTy PointTy :=
  .branch (.comp (.pair sample (.const .nat 64)) .natLe)
    (.pair (signed (Code.add literalX (.const .nat 64)) sample)
      (pos (Code.add (Code.mul (.const .nat 512) blockStart) (.const .nat 128))))
    (.pair (pos literalX)
      (pos (Code.add (Code.add (Code.mul (.const .nat 512) blockStart) (.const .nat 64)) sample)))

def exitPoint : Code SampleTy PointTy :=
  .branch (.comp (.pair sample (.const .nat 60)) .natLe)
    (.pair (pos literalX)
      (pos (Code.add (Code.add (Code.mul (.const .nat 512) blockEnd) (.const .nat 4)) sample)))
    (.pair (signed (Code.add literalX sample) (.const .nat 60))
      (pos (Code.add (Code.mul (.const .nat 512) blockEnd) (.const .nat 64))))

def betweenPoint : Code SampleTy PointTy :=
  .pair (pos literalX)
    (pos (Code.add (Code.add (Code.mul (.const .nat 512) (Code.add blockStart linkIndex))
      (.const .nat 4)) sample))

private theorem literalX_eval (x : SatTy.denote) (v i k : Nat) :
    literalX.eval (((x,v),i),k)=1536*x.length+577 := rfl
private theorem signed_eval (a b : Code SampleTy .nat) (z : SampleTy.denote) :
    (signed a b).eval z=encodeInt ((a.eval z:Int)-b.eval z) := normalize_eval _

theorem entryPoint_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) (i k : Nat) :
    entryPoint.eval (((x,v.val),i),k)=encodePoint
      (SatVariableLattice.entryPoint (3*x.length) (SatVariableOrder.prefix (finiteFormula x) v) k) := by
  simp only [entryPoint,pos,signed,literalX,blockStart,sample,Code.add,Code.mul,Code.eval,
    normalize_eval,integer,prefixCode_eval x v,decide_eq_true_eq,SatVariableLattice.entryPoint]
  split_ifs <;> simp only [SatVariableLattice.entryY,SatVariableLattice.wireX,encodePoint,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.sub_zero]
  all_goals congr 2 <;> ring

theorem exitPoint_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1)) (i k : Nat) :
    exitPoint.eval (((x,v.val),i),k)=encodePoint
      (SatVariableLattice.exitPoint (3*x.length)
        (SatVariableOrder.prefix (finiteFormula x) v+SatVariableOrder.count (finiteFormula x) v) k) := by
  simp only [exitPoint,pos,signed,literalX,blockEnd,sample,Code.add,Code.mul,Code.eval,
    normalize_eval,integer,prefixCode_eval x v,SatVariablePositionCode.count_eval x v,
    decide_eq_true_eq,SatVariableLattice.exitPoint]
  split_ifs <;> simp only [SatVariableLattice.exitY,SatVariableLattice.wireX,encodePoint,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.sub_zero]
  all_goals congr 2 <;> ring

theorem betweenPoint_eval (x : SatTy.denote) (v : Fin ((vsOf x).length +1))
    (i : Fin (SatVariableOrder.count (finiteFormula x) v)) (k : Nat) :
    betweenPoint.eval (((x,v.val),i.val+1),k)=encodePoint
      (SatVariableLattice.wireX (3*x.length),
        512*((SatWireLayout.variableRank (finiteFormula x)
          (SatVariableOrder.indexedOccurrence (finiteFormula x) v i)).val+1:Int)+4+k) := by
  simp only [betweenPoint,Code.eval,pos,signed,normalize_eval,integer,Code.add,Code.mul,literalX,
    blockStart,linkIndex,sample,prefixCode_eval x v,SatVariableOrder.variableRank_indexed,
    SatVariableLattice.wireX,encodePoint,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.sub_zero]
  congr 2 <;> ring

def fixedRoute (n : Nat) (p : Code SampleTy PointTy) : Code LinkTy CycleInputTy :=
  .comp (.pair .id (.const (.list .nat) (List.range n))) (.listMapEnv p)

def code : Code LinkTy CycleInputTy :=
  .branch (.comp (.pair .snd (.const .nat 0)) .natEq) (fixedRoute 445 entryPoint)
    (.branch (.comp (.pair .snd (.comp .fst SatVariablePositionCode.count)) .natEq)
      (fixedRoute 125 exitPoint) (fixedRoute 505 betweenPoint))

attribute [local irreducible] List.range entryPoint exitPoint betweenPoint

theorem code_eval (x : SatTy.denote) (e : SatVariableChainDrawing.Edge (finiteFormula x)) :
    code.eval ((x,(SatVariableChainDrawing.owner e).val),SatVariableChainDrawing.chainIndex e)=
      (SatVariableChainDrawing.route e).map encodePoint := by
  cases e with
  | entry v h =>
    change (List.range 445).map (fun k => entryPoint.eval (((x,v.val),0),k))=_
    simp only [entryPoint_eval x v,SatVariableChainDrawing.route,SatVariableLattice.entryRoute,
      List.map_map,Function.comp_def]
  | exit v h =>
    simp only [SatVariableChainDrawing.owner,SatVariableChainDrawing.chainIndex,
      code,Code.eval,SatVariablePositionCode.count_eval x v,decide_eq_true_eq,ite_eq_right (by omega :
        ¬SatVariableOrder.count (finiteFormula x) v=0),ite_true]
    change (List.range 125).map (fun k => exitPoint.eval (((x,v.val),_),k))=_
    simp only [exitPoint_eval x v,SatVariableChainDrawing.route,SatVariableLattice.exitRoute,
      List.map_map,Function.comp_def]
  | between v i j h =>
    have hi : i.val+1≠SatVariableOrder.count (finiteFormula x) v := by omega
    simp only [SatVariableChainDrawing.owner,SatVariableChainDrawing.chainIndex,
      code,Code.eval,SatVariablePositionCode.count_eval x v,decide_eq_true_eq,Nat.add_one_ne_zero,ite_false,ite_eq_right hi]
    change (List.range 505).map (fun k => betweenPoint.eval (((x,v.val),i.val+1),k))=_
    simp only [betweenPoint_eval x v i,SatVariableChainDrawing.route,SatVariableLattice.betweenRoute,
      SatCrossingRouting.rising,List.map_map,Function.comp_def]

end GridHardness.SatVariableChainRouteCode
